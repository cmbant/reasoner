module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Geometry
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryCollision

/-!
# Paper J, Layer 2 (L2.G4 (c)): the margins of the allowed interval, lem:tha-geom (c)

Proves `GeomMargins` of `TheoremA/GeometryStatements.lean` (frozen; not edited).  Two parts.

* Localisation (finding F-geom2): at `mu_0 in K` each energy of `J` has a pair `p < q` of allowed points
  (`T(p) > 0`, `T(q) > 0`, from `GeomBulk`); these positivities are open in `(mu, X)`, so they persist on a
  neighbourhood `N` of `mu_0` and a ball around the energy.  A finite subcover of `J` gives the closed pieces `J_nu`
  and the margins `c' = p + delta_1`, `c = q - delta_1`: then `u_- <= p` and `u_+ >= q`.
* The derivative bound at non-collision energies: a compactness argument on the zero set of `T` in `K x J x [0, L]`,
  where `|T'| > 0` by `GeomBulk`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.Margins

open Set Filter Topology FormalResearch.JacobiEigenvectors.Setting

/-- Positivity of `T(p; .,.)` near a point with `T(p) > 0`, uniformly on a neighbourhood `N` of `mu_0` in `K`
and a ball around `X_0`. -/
lemma loc_pos {Par : Type*} [TopologicalSpace Par] {L : ℝ} {K : Set Par} {G B : Par → ℝ → ℝ}
    (hcG : ContinuousOn (fun p : Par × ℝ => G p.1 p.2) (K ×ˢ Icc 0 L))
    (hcB : ContinuousOn (fun p : Par × ℝ => B p.1 p.2) (K ×ˢ Icc 0 L))
    {μ0 : Par} (hμ0 : μ0 ∈ K) {X0 p : ℝ} (hp : p ∈ Icc 0 L)
    (hpos : 0 < Tfun L (G μ0) (B μ0) X0 p) :
    ∃ N ∈ 𝓝[K] μ0, ∃ r > 0, ∀ μ ∈ N, μ ∈ K → ∀ X, dist X X0 < r → 0 < Tfun L (G μ) (B μ) X p := by
  have hmapG : MapsTo (fun z : Par × ℝ => (z.1, p)) (K ×ˢ univ) (K ×ˢ Icc 0 L) :=
    fun z hz => ⟨hz.1, hp⟩
  have hgp : ContinuousOn (fun z : Par × ℝ => G z.1 p) (K ×ˢ univ) :=
    hcG.comp (Continuous.prodMk continuous_fst continuous_const).continuousOn hmapG
  have hbp : ContinuousOn (fun z : Par × ℝ => B z.1 p) (K ×ˢ univ) :=
    hcB.comp (Continuous.prodMk continuous_fst continuous_const).continuousOn hmapG
  have hTc : ContinuousOn (fun z : Par × ℝ => Tfun L (G z.1) (B z.1) z.2 p) (K ×ˢ univ) := by
    unfold Tfun E0
    exact (continuousOn_const.mul (continuousOn_const.mul hgp)).sub
      ((continuous_snd.continuousOn.sub hbp).pow 2)
  have hev : ∀ᶠ z in 𝓝[K ×ˢ univ] (μ0, X0), 0 < Tfun L (G z.1) (B z.1) z.2 p :=
    Filter.Tendsto.eventually (hTc.continuousWithinAt ⟨hμ0, mem_univ X0⟩) (lt_mem_nhds hpos)
  have hev2 := eventually_nhdsWithin_iff.1 hev
  rw [nhds_prod_eq] at hev2
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hev2
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 hpb
  refine ⟨{μ | pa μ}, eventually_nhdsWithin_of_eventually_nhds hpa, r, hr, fun μ hμ hμK X hX => ?_⟩
  exact hab hμ (hr' hX) ⟨hμK, mem_univ X⟩

/-- Two allowed points `p < q` strictly inside the allowed interval, in `[0, L]`. -/
lemma pq_of_bulk {L g : ℝ} {G B : ℝ → ℝ} (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ} (h1 : Xsm L G B < X) (h2 : X < Xsp L G B) :
    ∃ p q : ℝ, p ∈ Icc 0 L ∧ q ∈ Icc 0 L ∧ p < q ∧ 0 < Tfun L G B X p ∧ 0 < Tfun L G B X q := by
  have hb := HypMorse.geomBulk L G B g hL hyp hG2 hB2 X h1 h2
  obtain ⟨hab, hiff, -, -, -, -, -, -⟩ := hb
  have ha0 : 0 ≤ uMinusS L G B X := by
    unfold uMinusS allowedSet
    apply Real.sInf_nonneg
    intro x hx
    exact hx.1.1
  have hbL : uPlusS L G B X ≤ L := by
    unfold uPlusS allowedSet
    apply Real.sSup_le
    · intro x hx
      exact hx.1.2
    · exact hL.le
  set a := uMinusS L G B X with ha
  set b := uPlusS L G B X with hb'
  have hp : (2 * a + b) / 3 ∈ Icc 0 L := ⟨by linarith, by linarith⟩
  have hq : (a + 2 * b) / 3 ∈ Icc 0 L := ⟨by linarith, by linarith⟩
  refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, hp, hq, by linarith, ?_, ?_⟩
  · exact (hiff _ hp).2 ⟨by linarith, by linarith⟩
  · exact (hiff _ hq).2 ⟨by linarith, by linarith⟩

/-- A positive lower bound for finitely many positive numbers. -/
lemma exists_pos_le_all {ι : Type*} [Finite ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ > 0, ∀ i, δ ≤ d i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min d
    exact ⟨d i0, hd i0, hi0⟩

/-- The localisation (first conjunct of lem:tha-geom (c)) at one point `mu_0 in K`. -/
lemma partA {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (g : ℝ)
    (hg : ∀ μ ∈ K, Hyp F.L (F.G 0 μ) (F.B 0 μ) g) (hR : PrincipalReg F K 2)
    (J : Set ℝ) (hJ : IsCompact J) (hJband : ∀ μ ∈ K, ∀ X ∈ J, F.bandLo μ < X ∧ X < F.bandHi μ)
    (μ0 : Par) (hμ0 : μ0 ∈ K) :
    ∃ N ∈ 𝓝[K] μ0, ∃ (n : ℕ) (Jν : Fin n → Set ℝ) (c' c : Fin n → ℝ) (δ1 : ℝ), 0 < δ1 ∧
      (∀ X ∈ J, ∃ ν, X ∈ Jν ν) ∧ (∀ ν, IsClosed (Jν ν) ∧ Jν ν ⊆ J) ∧ (∀ ν, c' ν < c ν) ∧
      ∀ ν, ∀ μ ∈ N, μ ∈ K → ∀ X ∈ Jν ν, F.uMinus μ X + δ1 ≤ c' ν ∧ c ν ≤ F.uPlus μ X - δ1 := by
  have hcG : ContinuousOn (fun p : Par × ℝ => F.G 0 p.1 p.2) (K ×ˢ Icc 0 F.L) := by
    simpa using hR.1.2 0 (Nat.zero_le _)
  have hcB : ContinuousOn (fun p : Par × ℝ => F.B 0 p.1 p.2) (K ×ˢ Icc 0 F.L) := by
    simpa using hR.2.2 0 (Nat.zero_le _)
  have hC2G : ∀ μ ∈ K, ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) := fun μ hμ => by
    simpa using hR.1.1 μ hμ
  have hC2B : ∀ μ ∈ K, ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) := fun μ hμ => by
    simpa using hR.2.1 μ hμ
  -- for each energy `X0`, a pair `p < q` of allowed points, stable near `(mu_0, X_0)`
  have hP : ∀ X0 : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ N ∈ 𝓝[K] μ0, ∃ p q : ℝ, (X0 ∈ J →
      (p ∈ Icc 0 F.L ∧ q ∈ Icc 0 F.L ∧ p < q ∧ ∀ μ ∈ N, μ ∈ K → ∀ X, dist X X0 < r →
        0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) X p ∧ 0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) X q)) := by
    intro X0
    by_cases hX0 : X0 ∈ J
    · obtain ⟨p, q, hp, hq, hpq, hTp, hTq⟩ :=
        pq_of_bulk F.L_pos (hg μ0 hμ0) (hC2G μ0 hμ0) (hC2B μ0 hμ0)
          (hJband μ0 hμ0 X0 hX0).1 (hJband μ0 hμ0 X0 hX0).2
      obtain ⟨Np, hNp, rp, hrp, hPp⟩ := loc_pos hcG hcB hμ0 hp hTp
      obtain ⟨Nq, hNq, rq, hrq, hPq⟩ := loc_pos hcG hcB hμ0 hq hTq
      refine ⟨min rp rq, lt_min hrp hrq, Np ∩ Nq, inter_mem hNp hNq, p, q,
        fun _ => ⟨hp, hq, hpq, ?_⟩⟩
      intro μ hμ hμK X hX
      exact ⟨hPp μ hμ.1 hμK X (lt_of_lt_of_le hX (min_le_left _ _)),
        hPq μ hμ.2 hμK X (lt_of_lt_of_le hX (min_le_right _ _))⟩
    · exact ⟨1, one_pos, univ, univ_mem, 0, 0, fun h => absurd h hX0⟩
  choose r hr N hN p q hpq using hP
  -- a finite subcover of `J` by the half balls of the radii `r`
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover (fun X0 : J => Metric.ball (X0 : ℝ) (r X0 / 2))
    (fun _ => Metric.isOpen_ball)
    (fun X hX => Set.mem_iUnion.2 ⟨⟨X, hX⟩, Metric.mem_ball_self (half_pos (hr X))⟩)
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin t.card → J, ∀ ν, idx ν = (t.equivFin.symm ν).1 := ⟨_, fun _ => rfl⟩
  have hsurj : ∀ i ∈ t, ∃ ν, idx ν = i := fun i hi =>
    ⟨t.equivFin ⟨i, hi⟩, by rw [hidx, Equiv.symm_apply_apply]⟩
  have hpqν : ∀ ν, p (idx ν : ℝ) ∈ Icc 0 F.L ∧ q (idx ν : ℝ) ∈ Icc 0 F.L ∧ p (idx ν : ℝ) < q (idx ν : ℝ) ∧
      ∀ μ ∈ N (idx ν : ℝ), μ ∈ K → ∀ X, dist X (idx ν : ℝ) < r (idx ν : ℝ) →
        0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) X (p (idx ν : ℝ)) ∧
          0 < Tfun F.L (F.G 0 μ) (F.B 0 μ) X (q (idx ν : ℝ)) :=
    fun ν => hpq (idx ν : ℝ) (idx ν).2
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_all
    (fun ν : Fin t.card => (q (idx ν : ℝ) - p (idx ν : ℝ)) / 3)
    (fun ν => by have := (hpqν ν).2.2.1; linarith)
  have hcover : ∀ X ∈ J, ∃ ν : Fin t.card,
      X ∈ J ∩ Metric.closedBall (idx ν : ℝ) (r (idx ν : ℝ) / 2) := by
    intro X hX
    obtain ⟨i, hi, hXi⟩ := Set.mem_iUnion₂.1 (ht hX)
    obtain ⟨ν, hν⟩ := hsurj i hi
    exact ⟨ν, hX, by rw [hν]; exact Metric.ball_subset_closedBall hXi⟩
  have hmain : ∀ ν : Fin t.card, ∀ μ ∈ {μ | ∀ ν' : Fin t.card, μ ∈ N (idx ν' : ℝ)}, μ ∈ K →
      ∀ X ∈ J ∩ Metric.closedBall (idx ν : ℝ) (r (idx ν : ℝ) / 2),
        F.uMinus μ X + δ ≤ p (idx ν : ℝ) + δ ∧ q (idx ν : ℝ) - δ ≤ F.uPlus μ X - δ := by
    intro ν μ hμN hμK X hX
    have hdist : dist X (idx ν : ℝ) < r (idx ν : ℝ) := by
      have := Metric.mem_closedBall.1 hX.2
      linarith [hr (idx ν : ℝ)]
    obtain ⟨hpI, hqI, -, hP'⟩ := hpqν ν
    have hTp := (hP' μ (hμN ν) hμK X hdist).1
    have hTq := (hP' μ (hμN ν) hμK X hdist).2
    have hup : F.uMinus μ X ≤ p (idx ν : ℝ) := by
      show sInf (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}) ≤ p (idx ν : ℝ)
      exact csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨hpI, hTp.le⟩
    have hvq : q (idx ν : ℝ) ≤ F.uPlus μ X := by
      show q (idx ν : ℝ) ≤ sSup (Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u})
      exact le_csSup ⟨F.L, fun x hx => hx.1.2⟩ ⟨hqI, hTq.le⟩
    exact ⟨by linarith, by linarith⟩
  refine ⟨{μ | ∀ ν : Fin t.card, μ ∈ N (idx ν : ℝ)}, Filter.eventually_all.2 (fun ν => hN (idx ν : ℝ)),
    t.card, fun ν => J ∩ Metric.closedBall (idx ν : ℝ) (r (idx ν : ℝ) / 2),
    fun ν => p (idx ν : ℝ) + δ, fun ν => q (idx ν : ℝ) - δ, δ, hδpos, hcover,
    fun ν => ⟨hJ.isClosed.inter Metric.isClosed_closedBall, Set.inter_subset_left⟩, ?_, ?_⟩
  · intro ν
    show p (idx ν : ℝ) + δ < q (idx ν : ℝ) - δ
    linarith [hδle ν]
  · intro ν μ hμN hμK X hX
    exact hmain ν μ hμN hμK X hX

/-- The two ends of the allowed interval are zeros of `T` in `[0, L]`, with `u_- < u_+`. -/
lemma ends_bulk {L g : ℝ} {G B : ℝ → ℝ} (hL : 0 < L) (hyp : Hyp L G B g) (hG2 : ContDiffOn ℝ 2 G (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ} (h1 : Xsm L G B < X) (h2 : X < Xsp L G B) :
    Tfun L G B X (uMinusS L G B X) = 0 ∧ uMinusS L G B X ∈ Icc 0 L ∧
      Tfun L G B X (uPlusS L G B X) = 0 ∧ uPlusS L G B X ∈ Icc 0 L ∧
      uMinusS L G B X < uPlusS L G B X := by
  have hb := HypMorse.geomBulk L G B g hL hyp hG2 hB2 X h1 h2
  obtain ⟨hab, -, -, hzeroiff, -, -, -, -⟩ := hb
  have ha0 : 0 ≤ uMinusS L G B X := by
    unfold uMinusS allowedSet
    apply Real.sInf_nonneg
    intro x hx
    exact hx.1.1
  have hbL : uPlusS L G B X ≤ L := by
    unfold uPlusS allowedSet
    apply Real.sSup_le
    · intro x hx
      exact hx.1.2
    · exact hL.le
  have hamem : uMinusS L G B X ∈ Icc 0 L := ⟨ha0, by linarith⟩
  have hbmem : uPlusS L G B X ∈ Icc 0 L := ⟨by linarith, hbL⟩
  exact ⟨(hzeroiff _ hamem).2 (Or.inl rfl), hamem, (hzeroiff _ hbmem).2 (Or.inr rfl), hbmem, hab⟩

/-- A zero of `T` in `[0, L]` at a non-collision energy is an interior point where `T' != 0`. -/
lemma zero_interior {L g : ℝ} {G B : ℝ → ℝ} (hL : 0 < L) (hyp : Hyp L G B g)
    (hG2 : ContDiffOn ℝ 2 G (Icc 0 L)) (hB2 : ContDiffOn ℝ 2 B (Icc 0 L)) {X : ℝ}
    (h1 : Xsm L G B < X) (h2 : X < Xsp L G B) (hX0 : X ≠ B 0) (hXL : X ≠ B L) {u : ℝ}
    (hu : u ∈ Icc 0 L) (hT : Tfun L G B X u = 0) :
    u ∈ Ioo 0 L ∧ deriv (Tfun L G B X) u ≠ 0 := by
  have hb := HypMorse.geomBulk L G B g hL hyp hG2 hB2 X h1 h2
  obtain ⟨hab, -, -, hzeroiff, hd0, hdL, h0iff, hLiff⟩ := hb
  obtain ⟨-, hMmem, -, hPmem, hMP⟩ := ends_bulk hL hyp hG2 hB2 h1 h2
  rcases (hzeroiff u hu).1 hT with h | h
  · have hMpos : 0 < uMinusS L G B X :=
      lt_of_le_of_ne hMmem.1 (fun h0 => hX0 (h0iff.1 h0.symm))
    refine ⟨⟨by rw [h]; exact hMpos, by rw [h]; exact lt_of_lt_of_le hMP hPmem.2⟩, ?_⟩
    rw [h]
    exact hd0 hMpos
  · have hPpos : 0 < uPlusS L G B X := lt_of_le_of_lt hMmem.1 hMP
    have hPL : uPlusS L G B X < L :=
      lt_of_le_of_ne hPmem.2 (fun e => hXL (hLiff.1 e))
    refine ⟨⟨by rw [h]; exact hPpos, by rw [h]; exact hPL⟩, ?_⟩
    rw [h]
    exact hdL hPL

/-- The derivative of `T(.; X)` at an interior point, in the form used by the penalty. -/
lemma deriv_Tfun_int {L X u : ℝ} {G B : ℝ → ℝ} (hu : u ∈ Ioo 0 L) (hG : DifferentiableOn ℝ G (Icc 0 L))
    (hB : DifferentiableOn ℝ B (Icc 0 L)) :
    deriv (Tfun L G B X) u = 4 * Collision.Dfn L G u + 2 * (X - B u) * derivWithin B (Icc 0 L) u := by
  have hGd : DifferentiableAt ℝ G u := hG.differentiableAt (Icc_mem_nhds hu.1 hu.2)
  have hBd : DifferentiableAt ℝ B u := hB.differentiableAt (Icc_mem_nhds hu.1 hu.2)
  have hT := (((Collision.hasDerivAt_E0' (L := L) hGd)).const_mul 4).sub ((hBd.hasDerivAt.const_sub X).pow 2)
  have hG' : deriv G u = derivWithin G (Icc 0 L) u :=
    (derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)).symm
  have hB' : deriv B u = derivWithin B (Icc 0 L) u :=
    (derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)).symm
  rw [show deriv (Tfun L G B X) u = deriv ((fun y => 4 * E0 L G y) - (fun x => X - B x) ^ 2) u from rfl,
    hT.deriv, hG', hB']
  unfold Collision.Dfn
  norm_num

/-- The derivative bound at non-collision energies (second conjunct of lem:tha-geom (c)).  The zero set of `T`
in `K x J x [0, L]` with the energy conditions is a sublevel set of a continuous penalty, hence compact; on it
`|T'| > 0` by `GeomBulk`, and the minimum of `|T'|` bounds `|T'(u_pm)|` from below. -/
lemma partB {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) (g : ℝ)
    (hK : IsCompact K) (hg : ∀ μ ∈ K, Hyp F.L (F.G 0 μ) (F.B 0 μ) g) (hR : PrincipalReg F K 2)
    (J : Set ℝ) (hJ : IsCompact J) (hJband : ∀ μ ∈ K, ∀ X ∈ J, F.bandLo μ < X ∧ X < F.bandHi μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cT : ℝ, 0 < cT ∧ ∀ μ ∈ K, ∀ X ∈ J, ε ≤ |X - F.B 0 μ 0| → ε ≤ |X - F.B 0 μ F.L| →
      cT ≤ |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uMinus μ X)| ∧
      cT ≤ |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uPlus μ X)| := by
  have hcG : ContinuousOn (fun p : Par × ℝ => F.G 0 p.1 p.2) (K ×ˢ Icc 0 F.L) := by
    simpa using hR.1.2 0 (Nat.zero_le _)
  have hcB : ContinuousOn (fun p : Par × ℝ => F.B 0 p.1 p.2) (K ×ˢ Icc 0 F.L) := by
    simpa using hR.2.2 0 (Nat.zero_le _)
  have hdG : ContinuousOn (fun p : Par × ℝ => derivWithin (F.G 0 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) := by
    simpa [iteratedDerivWithin_one] using hR.1.2 1 (by norm_num)
  have hdB : ContinuousOn (fun p : Par × ℝ => derivWithin (F.B 0 p.1) (Icc 0 F.L) p.2) (K ×ˢ Icc 0 F.L) := by
    simpa [iteratedDerivWithin_one] using hR.2.2 1 (by norm_num)
  have hC2G : ∀ μ ∈ K, ContDiffOn ℝ 2 (F.G 0 μ) (Icc 0 F.L) := fun μ hμ => by
    simpa using hR.1.1 μ hμ
  have hC2B : ∀ μ ∈ K, ContDiffOn ℝ 2 (F.B 0 μ) (Icc 0 F.L) := fun μ hμ => by
    simpa using hR.2.1 μ hμ
  have hdiffG : ∀ μ ∈ K, DifferentiableOn ℝ (F.G 0 μ) (Icc 0 F.L) := fun μ hμ =>
    (hC2G μ hμ).differentiableOn (by norm_num)
  have hdiffB : ∀ μ ∈ K, DifferentiableOn ℝ (F.B 0 μ) (Icc 0 F.L) := fun μ hμ =>
    (hC2B μ hμ).differentiableOn (by norm_num)
  -- the compact set `K x (J x [0, L])` of triples `(mu, X, u)`
  have hS : IsCompact (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := hK.prod (hJ.prod isCompact_Icc)
  have contU : Continuous (fun z : Par × ℝ × ℝ => (z.1, z.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have contB0 : Continuous (fun z : Par × ℝ × ℝ => (z.1, (0 : ℝ))) := continuous_fst.prodMk continuous_const
  have contBL : Continuous (fun z : Par × ℝ × ℝ => (z.1, F.L)) := continuous_fst.prodMk continuous_const
  have mapU : MapsTo (fun z : Par × ℝ × ℝ => (z.1, z.2.2)) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) (K ×ˢ Icc 0 F.L) :=
    fun z hz => ⟨hz.1, hz.2.2⟩
  have mapB0 : MapsTo (fun z : Par × ℝ × ℝ => (z.1, (0 : ℝ))) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L))
      (K ×ˢ Icc 0 F.L) := fun z hz => ⟨hz.1, ⟨le_rfl, F.L_pos.le⟩⟩
  have mapBL : MapsTo (fun z : Par × ℝ × ℝ => (z.1, F.L)) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L))
      (K ×ˢ Icc 0 F.L) := fun z hz => ⟨hz.1, ⟨F.L_pos.le, le_rfl⟩⟩
  have hGu : ContinuousOn (fun z : Par × ℝ × ℝ => F.G 0 z.1 z.2.2) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) :=
    hcG.comp contU.continuousOn mapU
  have hBu : ContinuousOn (fun z : Par × ℝ × ℝ => F.B 0 z.1 z.2.2) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) :=
    hcB.comp contU.continuousOn mapU
  have hdGu : ContinuousOn (fun z : Par × ℝ × ℝ => derivWithin (F.G 0 z.1) (Icc 0 F.L) z.2.2)
      (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := hdG.comp contU.continuousOn mapU
  have hdBu : ContinuousOn (fun z : Par × ℝ × ℝ => derivWithin (F.B 0 z.1) (Icc 0 F.L) z.2.2)
      (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := hdB.comp contU.continuousOn mapU
  have hB0S : ContinuousOn (fun z : Par × ℝ × ℝ => F.B 0 z.1 0) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) :=
    hcB.comp contB0.continuousOn mapB0
  have hBLS : ContinuousOn (fun z : Par × ℝ × ℝ => F.B 0 z.1 F.L) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) :=
    hcB.comp contBL.continuousOn mapBL
  have hXS : Continuous (fun z : Par × ℝ × ℝ => z.2.1) := continuous_fst.comp continuous_snd
  have hUS : Continuous (fun z : Par × ℝ × ℝ => z.2.2) := continuous_snd.comp continuous_snd
  have hTS : ContinuousOn (fun z : Par × ℝ × ℝ => Tfun F.L (F.G 0 z.1) (F.B 0 z.1) z.2.1 z.2.2)
      (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := by
    unfold Tfun E0
    exact (continuousOn_const.mul ((hUS.continuousOn.mul (continuousOn_const.sub hUS.continuousOn)).mul
      hGu)).sub ((hXS.continuousOn.sub hBu).pow 2)
  -- the penalty `f` (its sublevel set `{f <= 0}` is the zero set with the energy conditions) and `Phi = |T'|`
  obtain ⟨f, hf⟩ : ∃ f : Par × ℝ × ℝ → ℝ, f = fun z => max |Tfun F.L (F.G 0 z.1) (F.B 0 z.1) z.2.1 z.2.2|
      (max (ε - |z.2.1 - F.B 0 z.1 0|) (ε - |z.2.1 - F.B 0 z.1 F.L|)) := ⟨_, rfl⟩
  have hfS : ContinuousOn f (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := by
    rw [hf]
    have cmax : ∀ {a b : Par × ℝ × ℝ → ℝ}, ContinuousOn a (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) →
        ContinuousOn b (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) →
        ContinuousOn (fun z => max (a z) (b z)) (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) :=
      fun ha hb => continuous_max.comp_continuousOn (ha.prodMk hb)
    refine cmax (continuous_abs.comp_continuousOn hTS) (cmax ?_ ?_)
    · exact continuousOn_const.sub (continuous_abs.comp_continuousOn (hXS.continuousOn.sub hB0S))
    · exact continuousOn_const.sub (continuous_abs.comp_continuousOn (hXS.continuousOn.sub hBLS))
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Par × ℝ × ℝ → ℝ, Φ = fun z => |4 * Collision.Dfn F.L (F.G 0 z.1) z.2.2 +
      2 * (z.2.1 - F.B 0 z.1 z.2.2) * derivWithin (F.B 0 z.1) (Icc 0 F.L) z.2.2| := ⟨_, rfl⟩
  have hΦS : ContinuousOn Φ (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := by
    have hD : ContinuousOn (fun z : Par × ℝ × ℝ => Collision.Dfn F.L (F.G 0 z.1) z.2.2)
        (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) := by
      unfold Collision.Dfn
      apply ContinuousOn.add
      · exact (continuousOn_const.sub (continuousOn_const.mul hUS.continuousOn)).mul hGu
      · exact (hUS.continuousOn.mul (continuousOn_const.sub hUS.continuousOn)).mul hdGu
    rw [hΦ]
    exact continuous_abs.comp_continuousOn
      ((continuousOn_const.mul hD).add ((continuousOn_const.mul (hXS.continuousOn.sub hBu)).mul hdBu))
  have hZc : IsCompact ((K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) ∩ f ⁻¹' Iic 0) :=
    hfS.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hS 0
  -- on the zero set, `Phi > 0`
  have hpos : ∀ z ∈ (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) ∩ f ⁻¹' Iic 0, 0 < Φ z := by
    rintro z ⟨⟨hμ, hXJ, hu⟩, hfz⟩
    rw [hf] at hfz
    simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff] at hfz
    obtain ⟨hT0, hε0, hεL⟩ := hfz
    have hT : Tfun F.L (F.G 0 z.1) (F.B 0 z.1) z.2.1 z.2.2 = 0 := abs_nonpos_iff.1 hT0
    have hX0 : z.2.1 ≠ F.B 0 z.1 0 := by
      intro h
      rw [h, sub_self, abs_zero] at hε0
      linarith
    have hXL : z.2.1 ≠ F.B 0 z.1 F.L := by
      intro h
      rw [h, sub_self, abs_zero] at hεL
      linarith
    obtain ⟨hint, hder⟩ := zero_interior F.L_pos (hg z.1 hμ) (hC2G z.1 hμ) (hC2B z.1 hμ)
      (hJband z.1 hμ z.2.1 hXJ).1 (hJband z.1 hμ z.2.1 hXJ).2 hX0 hXL hu hT
    rw [hΦ]
    dsimp only
    rw [← deriv_Tfun_int hint (hdiffG z.1 hμ) (hdiffB z.1 hμ)]
    exact abs_pos.2 hder
  -- the zero set contains the energies `u_pm` of every admissible `(mu, X)`
  have hmem : ∀ μ ∈ K, ∀ X ∈ J, ε ≤ |X - F.B 0 μ 0| → ε ≤ |X - F.B 0 μ F.L| → ∀ u ∈ Icc 0 F.L,
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X u = 0 → (μ, X, u) ∈ (K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) ∩ f ⁻¹' Iic 0 := by
    intro μ hμ X hX h1 h2 u hu hT
    refine ⟨⟨hμ, hX, hu⟩, ?_⟩
    rw [hf]
    simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff]
    rw [hT, abs_zero]
    exact ⟨le_rfl, by linarith, by linarith⟩
  rcases ((K ×ˢ (J ×ˢ Icc (0 : ℝ) F.L)) ∩ f ⁻¹' Iic 0).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun μ hμ X hX h1 h2 => ?_⟩
    exfalso
    obtain ⟨hT0, hM, -, -, -⟩ := ends_bulk F.L_pos (hg μ hμ) (hC2G μ hμ) (hC2B μ hμ)
      (hJband μ hμ X hX).1 (hJband μ hμ X hX).2
    have hmemE := hmem μ hμ X hX h1 h2 _ hM hT0
    rw [hE] at hmemE
    exact hmemE
  · obtain ⟨zs, hzs, hmin⟩ := hZc.exists_isMinOn hne (hΦS.mono Set.inter_subset_left)
    refine ⟨Φ zs, hpos zs hzs, fun μ hμ X hX h1 h2 => ?_⟩
    obtain ⟨hT0, hM, hTP, hP, -⟩ := ends_bulk F.L_pos (hg μ hμ) (hC2G μ hμ) (hC2B μ hμ)
      (hJband μ hμ X hX).1 (hJband μ hμ X hX).2
    have hX0 : X ≠ F.B 0 μ 0 := by
      intro h
      rw [h, sub_self, abs_zero] at h1
      linarith
    have hXL : X ≠ F.B 0 μ F.L := by
      intro h
      rw [h, sub_self, abs_zero] at h2
      linarith
    have hM' : F.uMinus μ X ∈ Icc 0 F.L := hM
    have hP' : F.uPlus μ X ∈ Icc 0 F.L := hP
    have hTM : Tfun F.L (F.G 0 μ) (F.B 0 μ) X (F.uMinus μ X) = 0 := hT0
    have hTP' : Tfun F.L (F.G 0 μ) (F.B 0 μ) X (F.uPlus μ X) = 0 := hTP
    obtain ⟨hMI, -⟩ := zero_interior F.L_pos (hg μ hμ) (hC2G μ hμ) (hC2B μ hμ)
      (hJband μ hμ X hX).1 (hJband μ hμ X hX).2 hX0 hXL hM' hTM
    obtain ⟨hPI, -⟩ := zero_interior F.L_pos (hg μ hμ) (hC2G μ hμ) (hC2B μ hμ)
      (hJband μ hμ X hX).1 (hJband μ hμ X hX).2 hX0 hXL hP' hTP'
    have eqM : Φ (μ, X, F.uMinus μ X) = |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uMinus μ X)| := by
      rw [hΦ]
      dsimp only
      rw [deriv_Tfun_int hMI (hdiffG μ hμ) (hdiffB μ hμ)]
    have eqP : Φ (μ, X, F.uPlus μ X) = |deriv (Tfun F.L (F.G 0 μ) (F.B 0 μ) X) (F.uPlus μ X)| := by
      rw [hΦ]
      dsimp only
      rw [deriv_Tfun_int hPI (hdiffG μ hμ) (hdiffB μ hμ)]
    have hMmin : Φ zs ≤ Φ (μ, X, F.uMinus μ X) :=
      isMinOn_iff.1 hmin _ (hmem μ hμ X hX h1 h2 _ hM' hTM)
    have hPmin : Φ zs ≤ Φ (μ, X, F.uPlus μ X) :=
      isMinOn_iff.1 hmin _ (hmem μ hμ X hX h1 h2 _ hP' hTP')
    rw [eqM] at hMmin
    rw [eqP] at hPmin
    exact ⟨hMmin, hPmin⟩

/-- **lem:tha-geom (c)**, the margins: the localisation and the derivative bound. -/
theorem geomMargins {Par : Type*} [TopologicalSpace Par] (F : SymbolFamily Par) (K : Set Par) :
    GeomMargins F K := by
  unfold GeomMargins
  intro hK hH hR J hJ hJband
  obtain ⟨g, hg⟩ := hH
  exact ⟨fun μ0 hμ0 => partA F K g hg hR J hJ hJband μ0 hμ0,
    fun ε hε => partB F K g hK hg hR J hJ hJband ε hε⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Margins.geomMargins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.Margins.geomMargins

end FormalResearch.JacobiEigenvectors.TheoremA.Margins

module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenBase
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometryAll
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkProof
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCovered

/-!
# Paper J, Layer 2: assembly of thm:A (ii) from its cases; the bulk case of the relative clause R1 (L2.C9)

Source: Paper J `thmA.tex`, proof of `thm:A (ii)` and "The relative statement" (the *Bulk case*); `def:tha-Psihat`; frozen statements `ThmAi`, `ThmAii` (`Statements.lean`), `PropThaW`.
(There is no frozen `ThmA`: thm:A is `ThmAi F K M` together with `ThmAii F K m ...`.)

## Proved here (axiom-pinned)

* `tfun_lip`, `tfun_frozen_close`: the Lipschitz constant of `T(.; X)` from sup bounds of `G, B`, and `|T^{(h)} - T| <= C h` for the frozen principal symbols `G_0 + h G_1`, `B_0 + h B_1`.
* `collar_of_Tneg`: for principal symbols with `(H1)`--`(H3)` and `X` in the open band, `T(u; X) <= -e` with `T(.; X)` `Lam`-Lipschitz puts `u` at distance `>= e/(Lam+1)` from `[u_-, u_+]` (`lem:tha-geom` (a), `HypMorse.geomBulk`).
* `bulk_relative_collar`: for every `eps > 0` a collar `delta > 0` and `h_1 > 0`: sites with `T(u_n; X) <= -eps` (`T` of the principal symbols of `F` itself) at bulk energies `X in [Jlo, Jhi]` lie in the `delta`-collar of the
  frozen allowed interval at `(mu, h)`.  Uses `DM F K 1` (jets of order <= 1), `StdAssump` of the frozen family, `CI.cover`.
* `thmAii_bulk_relative`: **the bulk case of the relative clause of `ThmAii`** (`envVec <= C_eps |psiHatVec|` for eigenvalues in a bulk block) from the collar clause of `PropThaW` for every block.
* `AiiAbs`, `thmAii_of_cases` / `thmAii_of_cases'` (frozen form): `ThmAii` from its three cases (bulk block, upper soft window, lower soft window), with `spectrumCovered` (proved) giving the case split, constants combined by `max`
  (needs `hnn`, nonnegativity of the envelopes for small `h`, an `exists h_n` premise discharged in `ThmAAssemblySoft.lean`).  `thmAi_of_smoSpec`: `ThmAi` from `ThmSmoSpec`.

## Differences from the paper / findings

* **F-BB-4**: `PropThaW` has no conjunct `sum_n bulkEnv^2 <= C`, but `ThmAii` (first clause, second part) needs it (paper: "`sum (E M)^2 <= sum M_Web^2 <= C h^{-1/2}` while `hat N^2 ~ h^{-1/2}`"); `PropThaW2` has the analogue.
  Minimal correction: add `sum_{n in rowsOf N} (bulkEnv CL CR p X N n)^2 <= Cc` to the eigen-system clause of `PropThaW`.
* The relative clause needs `1 <= m`-free arguments only; `0 < t0` is not needed (it follows from `step N <= t0`).

## Not formalised

The cases `hB`, `hU`, `hL`, `rU`, `rL` of `thmAii_of_cases`: see `ThmAAssemblyCases.lean` for what is derived from `PropThaW`, `propThaW2_proved`, `stepZero`, `NegTransport`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- **Lipschitz constant of `T(.; X)` from bounds on the symbols** (pure algebra).  If `|G|, |B| <= M` and `G`, `B` are `Lam`-Lipschitz on `[0, L]` and `|X| <= MX`, then `T(.; X)` is
`(4 (L M + L^2 Lam) + Lam (2 MX + 2 M))`-Lipschitz there. -/
lemma tfun_lip {L : ℝ} {G B : ℝ → ℝ} {M Lam MX X : ℝ} (hL : 0 < L) (hLam : 0 ≤ Lam)
    (hGb : ∀ u ∈ Icc 0 L, |G u| ≤ M) (hBb : ∀ u ∈ Icc 0 L, |B u| ≤ M)
    (hGl : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, |G u - G v| ≤ Lam * |u - v|)
    (hBl : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, |B u - B v| ≤ Lam * |u - v|) (hX : |X| ≤ MX)
    {u v : ℝ} (hu : u ∈ Icc 0 L) (hv : v ∈ Icc 0 L) :
    |Tfun L G B X u - Tfun L G B X v| ≤ (4 * (L * M + L ^ 2 * Lam) + Lam * (2 * MX + 2 * M)) * |u - v| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hGb u hu)
  have hMX : 0 ≤ MX := (abs_nonneg _).trans hX
  have e : Tfun L G B X u - Tfun L G B X v =
      4 * ((u * (L - u) - v * (L - v)) * G u + v * (L - v) * (G u - G v)) - (B v - B u) * (2 * X - B u - B v) := by
    unfold Tfun E0; ring
  rw [e]
  have h1 : |u * (L - u) - v * (L - v)| ≤ L * |u - v| := by
    have : u * (L - u) - v * (L - v) = (u - v) * (L - u - v) := by ring
    rw [this, abs_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have h2 : |v * (L - v)| ≤ L ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hv.1 (by linarith [hv.2]))]
    nlinarith [hv.1, hv.2]
  have h3 : |(u * (L - u) - v * (L - v)) * G u| ≤ L * M * |u - v| := by
    rw [abs_mul]
    calc |u * (L - u) - v * (L - v)| * |G u| ≤ (L * |u - v|) * M :=
          mul_le_mul h1 (hGb u hu) (abs_nonneg _) (by positivity)
      _ = L * M * |u - v| := by ring
  have h4 : |v * (L - v) * (G u - G v)| ≤ L ^ 2 * Lam * |u - v| := by
    rw [abs_mul]
    calc |v * (L - v)| * |G u - G v| ≤ L ^ 2 * (Lam * |u - v|) :=
          mul_le_mul h2 (hGl u hu v hv) (abs_nonneg _) (by positivity)
      _ = L ^ 2 * Lam * |u - v| := by ring
  have h5 : |(B v - B u) * (2 * X - B u - B v)| ≤ Lam * (2 * MX + 2 * M) * |u - v| := by
    rw [abs_mul]
    have hb1 : |B v - B u| ≤ Lam * |u - v| := by rw [abs_sub_comm]; exact hBl u hu v hv
    have hb2 : |2 * X - B u - B v| ≤ 2 * MX + 2 * M := by
      have := hBb u hu
      have := hBb v hv
      calc |2 * X - B u - B v| ≤ |2 * X| + |B u| + |B v| := by
            calc _ ≤ |2 * X - B u| + |B v| := abs_sub _ _
              _ ≤ |2 * X| + |B u| + |B v| := by gcongr; exact abs_sub _ _
        _ ≤ 2 * MX + M + M := by
            have : |2 * X| = 2 * |X| := by rw [abs_mul]; norm_num
            linarith
        _ = 2 * MX + 2 * M := by ring
    calc |B v - B u| * |2 * X - B u - B v| ≤ (Lam * |u - v|) * (2 * MX + 2 * M) :=
          mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      _ = Lam * (2 * MX + 2 * M) * |u - v| := by ring
  calc |4 * ((u * (L - u) - v * (L - v)) * G u + v * (L - v) * (G u - G v)) - (B v - B u) * (2 * X - B u - B v)|
      ≤ |4 * ((u * (L - u) - v * (L - v)) * G u + v * (L - v) * (G u - G v))| + |(B v - B u) * (2 * X - B u - B v)| := abs_sub _ _
    _ ≤ 4 * (L * M * |u - v| + L ^ 2 * Lam * |u - v|) + Lam * (2 * MX + 2 * M) * |u - v| := by
        refine add_le_add ?_ h5
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h3 h4)) (by norm_num)
    _ = _ := by ring

/-- **`T` of the frozen principal symbols is `O(h)`-close to `T` of the principal symbols** (`G_0 + h G_1`, `B_0 + h B_1` against `G_0, B_0`; `0 <= h <= 1`). -/
lemma tfun_frozen_close {L : ℝ} {G0 G1 B0 B1 : ℝ → ℝ} {M MX X h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hG1 : ∀ u ∈ Icc 0 L, |G1 u| ≤ M) (hB1 : ∀ u ∈ Icc 0 L, |B1 u| ≤ M) (hB0 : ∀ u ∈ Icc 0 L, |B0 u| ≤ M) (hX : |X| ≤ MX)
    {u : ℝ} (hu : u ∈ Icc 0 L) :
    |Tfun L (fun s => G0 s + h * G1 s) (fun s => B0 s + h * B1 s) X u - Tfun L G0 B0 X u| ≤ h * (4 * L ^ 2 * M + M * (2 * MX + 2 * M + M)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hG1 u hu)
  have hMX : 0 ≤ MX := (abs_nonneg _).trans hX
  have e : Tfun L (fun s => G0 s + h * G1 s) (fun s => B0 s + h * B1 s) X u - Tfun L G0 B0 X u =
      h * (4 * (u * (L - u)) * G1 u + B1 u * (2 * (X - B0 u) - h * B1 u)) := by
    unfold Tfun E0; ring
  rw [e, abs_mul, abs_of_nonneg hh0]
  refine mul_le_mul_of_nonneg_left ?_ hh0
  have h1 : |4 * (u * (L - u)) * G1 u| ≤ 4 * L ^ 2 * M := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg (mul_nonneg hu.1 (by linarith [hu.2]))]
    have : u * (L - u) ≤ L ^ 2 := by nlinarith [hu.1, hu.2]
    exact mul_le_mul (by linarith) (hG1 u hu) (abs_nonneg _) (by positivity)
  have h2 : |B1 u * (2 * (X - B0 u) - h * B1 u)| ≤ M * (2 * MX + 2 * M + M) := by
    rw [abs_mul]
    have hb : |2 * (X - B0 u) - h * B1 u| ≤ 2 * MX + 2 * M + M := by
      have a1 : |X - B0 u| ≤ MX + M := (abs_sub _ _).trans (add_le_add hX (hB0 u hu))
      have a2 : |h * B1 u| ≤ M := by
        rw [abs_mul, abs_of_nonneg hh0]
        have := mul_le_mul hh1 (hB1 u hu) (abs_nonneg _) zero_le_one
        linarith
      calc |2 * (X - B0 u) - h * B1 u| ≤ |2 * (X - B0 u)| + |h * B1 u| := abs_sub _ _
        _ ≤ 2 * (MX + M) + M := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            linarith
        _ = 2 * MX + 2 * M + M := by ring
    exact mul_le_mul (hB1 u hu) hb (abs_nonneg _) hM
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **A site with `T <= -e` is a collar away from the allowed interval** (the geometric step of the bulk relative clause): for principal symbols with `(H1)`--`(H3)` and `X` in the open band, if `T(.; X)` is
`Lam`-Lipschitz on `[0, L]` and `T(u; X) <= -e < 0`, then `u` is at distance `>= e/(Lam + 1)` from `[u_-, u_+]` (by `lem:tha-geom` (a): `T = 0` exactly at `u_pm`, `T < 0` outside). -/
lemma collar_of_Tneg {L g : ℝ} {G0 B0 : ℝ → ℝ} (hL : 0 < L) (hyp : Hyp L G0 B0 g) (hG2 : ContDiffOn ℝ 2 G0 (Icc 0 L))
    (hB2 : ContDiffOn ℝ 2 B0 (Icc 0 L)) {X : ℝ} (hX1 : Xsm L G0 B0 < X) (hX2 : X < Xsp L G0 B0) {Lam e : ℝ} (hLam : 0 ≤ Lam)
    (he : 0 < e) (hLip : ∀ u ∈ Icc 0 L, ∀ v ∈ Icc 0 L, |Tfun L G0 B0 X u - Tfun L G0 B0 X v| ≤ Lam * |u - v|)
    {u : ℝ} (hu : u ∈ Icc 0 L) (hTu : Tfun L G0 B0 X u ≤ -e) :
    u + e / (Lam + 1) ≤ uMinusS L G0 B0 X ∨ uPlusS L G0 B0 X + e / (Lam + 1) ≤ u := by
  obtain ⟨hlt, hpos, hneg, hzero, -⟩ := HypMorse.geomBulk L G0 B0 g hL hyp hG2 hB2 X hX1 hX2
  -- the ends lie in [0, L]
  have hne : (allowedSet L G0 B0 X).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : uMinusS L G0 B0 X = uPlusS L G0 B0 X := by
      unfold uMinusS uPlusS; rw [hemp]; simp
    linarith
  have hsub : allowedSet L G0 B0 X ⊆ Icc 0 L := fun x hx => hx.1
  have hbdd : BddBelow (allowedSet L G0 B0 X) := ⟨0, fun x hx => hx.1.1⟩
  have hbdd' : BddAbove (allowedSet L G0 B0 X) := ⟨L, fun x hx => hx.1.2⟩
  obtain ⟨x0, hx0⟩ := hne
  have hum : uMinusS L G0 B0 X ∈ Icc 0 L :=
    ⟨le_csInf ⟨x0, hx0⟩ (fun x hx => hx.1.1), (csInf_le hbdd hx0).trans hx0.1.2⟩
  have hup : uPlusS L G0 B0 X ∈ Icc 0 L :=
    ⟨hx0.1.1.trans (le_csSup hbdd' hx0), csSup_le ⟨x0, hx0⟩ (fun x hx => hx.1.2)⟩
  have hTm : Tfun L G0 B0 X (uMinusS L G0 B0 X) = 0 := (hzero _ hum).2 (Or.inl rfl)
  have hTp : Tfun L G0 B0 X (uPlusS L G0 B0 X) = 0 := (hzero _ hup).2 (Or.inr rfl)
  have hout : u < uMinusS L G0 B0 X ∨ uPlusS L G0 B0 X < u := by
    by_contra hcon
    push Not at hcon
    have hin : u ∈ Icc (uMinusS L G0 B0 X) (uPlusS L G0 B0 X) := ⟨hcon.1, hcon.2⟩
    rcases eq_or_lt_of_le hin.1 with h1 | h1
    · rw [← h1, hTm] at hTu; linarith
    · rcases eq_or_lt_of_le hin.2 with h2 | h2
      · rw [h2, hTp] at hTu; linarith
      · have := (hpos u hu).2 ⟨h1, h2⟩
        linarith
  have key : ∀ w ∈ Icc (0 : ℝ) L, Tfun L G0 B0 X w = 0 → e ≤ Lam * |u - w| := by
    intro w hw hTw
    have := hLip u hu w hw
    rw [hTw, sub_zero] at this
    have h2 : e ≤ |Tfun L G0 B0 X u| := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hLp : 0 < Lam + 1 := by linarith
  rcases hout with h | h
  · left
    have := key _ hum hTm
    rw [abs_of_neg (by linarith)] at this
    have h2 : e / (Lam + 1) ≤ uMinusS L G0 B0 X - u := by
      rw [div_le_iff₀ hLp]
      nlinarith
    linarith
  · right
    have := key _ hup hTp
    rw [abs_of_pos (by linarith)] at this
    have h2 : e / (Lam + 1) ≤ u - uPlusS L G0 B0 X := by
      rw [div_le_iff₀ hLp]
      nlinarith
    linarith

/-- **The bulk case of the relative clause of `ThmAii`** (paper, "The relative statement", *Bulk case*): for every `eps > 0` there are `delta > 0` and `h_1 > 0` such that for `mu in K`, `h = step N <= min h_1 t0`,
every energy `X in [Jlo, Jhi]` of the bulk range and every row `n` with `T(u_n; X) <= -eps` (`T` of the principal symbols of `F` itself) lies in the `delta`-collar of the frozen allowed interval:
`u_n <= u_-^{(h)}(X) - delta` or `u_+^{(h)}(X) + delta <= u_n` (`u_pm^{(h)}` the turning points of the frozen family at `(mu, h)`), which is where the collar clause of `PropThaW` applies.
Proof: `|T^{(h)} - T| <= C h` (`tfun_frozen_close`, jets `G_1, B_1` bounded), so `T^{(h)}(u_n; X) <= -eps/2` for small `h`; `T^{(h)}(.; X)` is uniformly Lipschitz (`tfun_lip`, jets of order `<= 1`); and
`collar_of_Tneg` (`lem:tha-geom` (a) for the frozen principal symbols, `X` in the open band of `(mu, h)` by `hcov`). -/
theorem bulk_relative_collar {F : SymbolFamily Par} {K : Set Par} (hK : IsCompact K) (hD : DM F K 1) {Kidx r : ℕ} {t0 Jlo Jhi : ℝ}
    (hstd : StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r)
    (hcov : ∀ p ∈ paramSet K t0, (frozenFamily F Kidx).bandLo p < Jlo ∧ Jhi < (frozenFamily F Kidx).bandHi p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ h1 : ℝ, 0 < δ ∧ 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h1 → F.step N ≤ t0 → ∀ X ∈ Icc Jlo Jhi, ∀ n ∈ rowsOf N,
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) ≤ -ε →
        uNode (F.step N) n ≤ (frozenFamily F Kidx).uMinus (μ, F.step N) X - δ ∨
          (frozenFamily F Kidx).uPlus (μ, F.step N) X + δ ≤ uNode (F.step N) n := by
  obtain ⟨hPc, hE, ⟨g, hg⟩⟩ := hstd
  have hL := F.L_pos
  -- bounds of the jets of order 0 and 1 of G_0, G_1, B_0, B_1
  have hreg : ∀ j ≤ 1, JetReg (F.G j) K F.L (regBudget 1 - 10 * (j / 2)) ∧ JetReg (F.B j) K F.L (regBudget 1 - 10 * (j / 2)) := hD.reg
  have hrb : ∀ j ≤ 1, 1 ≤ regBudget 1 - 10 * (j / 2) := by
    intro j hj; unfold regBudget; omega
  have hjb : ∀ (f : ℕ → Par → ℝ → ℝ), (∀ j ≤ 1, JetReg (f j) K F.L (regBudget 1 - 10 * (j / 2))) →
      ∃ M Lam : ℝ, 0 ≤ M ∧ 0 ≤ Lam ∧ ∀ j ≤ 1, ∀ μ ∈ K, (∀ s ∈ Icc 0 F.L, |f j μ s| ≤ M) ∧
        ∀ s ∈ Icc 0 F.L, ∀ s' ∈ Icc 0 F.L, |f j μ s - f j μ s'| ≤ Lam * |s - s'| := by
    intro f hf
    have h0 : ∀ j, ∃ M0 M1 : ℝ, j ≤ 1 → ∀ μ ∈ K, (∀ s ∈ Icc 0 F.L, |f j μ s| ≤ M0) ∧ ∀ s ∈ Icc 0 F.L, |iteratedDerivWithin 1 (f j μ) (Icc 0 F.L) s| ≤ M1 := by
      intro j
      by_cases hj : j ≤ 1
      · obtain ⟨M0, hM0⟩ := jet_bound hK (hf j hj) (k := 0) (Nat.zero_le _)
        obtain ⟨M1, hM1⟩ := jet_bound hK (hf j hj) (k := 1) (hrb j hj)
        exact ⟨M0, M1, fun _ μ hμ => ⟨fun s hs => by simpa using hM0 μ hμ s hs, fun s hs => hM1 μ hμ s hs⟩⟩
      · exact ⟨0, 0, fun h => absurd h hj⟩
    choose M0 M1 hM using h0
    refine ⟨|M0 0| + |M0 1|, |M1 0| + |M1 1|, by positivity, by positivity, fun j hj μ hμ => ⟨fun s hs => ?_, fun s hs s' hs' => ?_⟩⟩
    · have := (hM j hj μ hμ).1 s hs
      have hj' : M0 j ≤ |M0 0| + |M0 1| := by
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> linarith [le_abs_self (M0 0), le_abs_self (M0 1), abs_nonneg (M0 0), abs_nonneg (M0 1)]
      exact this.trans hj'
    · have h1 := lip_of_iterDeriv_one (hrb j hj) ((hf j hj).1 μ hμ) (fun x hx => (hM j hj μ hμ).2 x hx) hs hs'
      have : M1 j ≤ |M1 0| + |M1 1| := by
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> linarith [le_abs_self (M1 0), le_abs_self (M1 1), abs_nonneg (M1 0), abs_nonneg (M1 1)]
      exact h1.trans (mul_le_mul_of_nonneg_right this (abs_nonneg _))
  obtain ⟨MG, LG, hMG, hLG, hGj⟩ := hjb (fun j => F.G j) (fun j hj => (hreg j hj).1)
  obtain ⟨MB, LB, hMB, hLB, hBj⟩ := hjb (fun j => F.B j) (fun j hj => (hreg j hj).2)
  set Mj : ℝ := MG + MB with hMj
  set Lj : ℝ := LG + LB with hLj
  have hMj0 : 0 ≤ Mj := by positivity
  have hLj0 : 0 ≤ Lj := by positivity
  set MX : ℝ := |Jlo| + |Jhi| with hMX
  set L : ℝ := F.L with hLdef
  set Ccl : ℝ := 4 * L ^ 2 * Mj + Mj * (2 * MX + 2 * Mj + Mj) with hCcl
  have hCcl0 : 0 ≤ Ccl := by positivity
  set Lam : ℝ := 4 * (L * (2 * Mj) + L ^ 2 * (2 * Lj)) + (2 * Lj) * (2 * MX + 2 * (2 * Mj)) with hLam
  have hLam0 : 0 ≤ Lam := by positivity
  refine ⟨ε / 2 / (Lam + 1), min 1 (ε / (2 * (Ccl + 1))), by positivity, lt_min one_pos (by positivity), ?_⟩
  intro μ hμ N hN hN' X hX n hn hT
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  set h := F.step N with hh
  have hN1 : h ≤ 1 := hN.trans (min_le_left _ _)
  have hN2 : h ≤ ε / (2 * (Ccl + 1)) := hN.trans (min_le_right _ _)
  have hp : (μ, h) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith [hpos, hN'], hN'⟩⟩
  obtain ⟨hband1, hband2⟩ := hcov _ hp
  have hhyp := hg _ hp
  -- C^2 regularity of the frozen principal symbols
  have h2le : (2 : WithTop ℕ∞) ≤ ((r - 10 * 0 : ℕ) : WithTop ℕ∞) := by
    have hb := hE.budget
    have : (2 : ℕ) ≤ r - 10 * 0 := by unfold regBudget at hb; omega
    exact_mod_cast this
  have hG2 : ContDiffOn ℝ 2 ((frozenFamily F Kidx).G 0 (μ, h)) (Icc 0 F.L) :=
    (((hE.reg 0 (Nat.zero_le _)).1.1 _ hp).of_le h2le)
  have hB2 : ContDiffOn ℝ 2 ((frozenFamily F Kidx).B 0 (μ, h)) (Icc 0 F.L) :=
    (((hE.reg 0 (Nat.zero_le _)).2.1 _ hp).of_le h2le)
  have hGfun : (frozenFamily F Kidx).G 0 (μ, h) = fun s => F.G 0 μ s + h * F.G 1 μ s := by
    funext s; simp [frozenFamily]
  have hBfun : (frozenFamily F Kidx).B 0 (μ, h) = fun s => F.B 0 μ s + h * F.B 1 μ s := by
    funext s; simp [frozenFamily]
  have hXb : |X| ≤ MX := by
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le Jlo, le_abs_self Jhi, abs_nonneg Jlo, abs_nonneg Jhi, hX.1, hX.2, le_abs_self Jlo, neg_abs_le Jhi]
  -- bounds for the frozen symbols
  have hGb : ∀ u ∈ Icc 0 F.L, |F.G 0 μ u + h * F.G 1 μ u| ≤ 2 * Mj := by
    intro u hu
    have a0 := (hGj 0 (by omega) μ hμ).1 u hu
    have a1 := (hGj 1 le_rfl μ hμ).1 u hu
    have : |h * F.G 1 μ u| ≤ MG := by
      rw [abs_mul, abs_of_nonneg hpos.le]
      calc h * |F.G 1 μ u| ≤ 1 * MG := mul_le_mul hN1 a1 (abs_nonneg _) zero_le_one
        _ = MG := one_mul _
    calc _ ≤ |F.G 0 μ u| + |h * F.G 1 μ u| := abs_add_le _ _
      _ ≤ 2 * Mj := by linarith
  have hBb : ∀ u ∈ Icc 0 F.L, |F.B 0 μ u + h * F.B 1 μ u| ≤ 2 * Mj := by
    intro u hu
    have a0 := (hBj 0 (by omega) μ hμ).1 u hu
    have a1 := (hBj 1 le_rfl μ hμ).1 u hu
    have : |h * F.B 1 μ u| ≤ MB := by
      rw [abs_mul, abs_of_nonneg hpos.le]
      calc h * |F.B 1 μ u| ≤ 1 * MB := mul_le_mul hN1 a1 (abs_nonneg _) zero_le_one
        _ = MB := one_mul _
    calc _ ≤ |F.B 0 μ u| + |h * F.B 1 μ u| := abs_add_le _ _
      _ ≤ 2 * Mj := by linarith
  have hGl : ∀ u ∈ Icc 0 F.L, ∀ v ∈ Icc 0 F.L, |(F.G 0 μ u + h * F.G 1 μ u) - (F.G 0 μ v + h * F.G 1 μ v)| ≤ (2 * Lj) * |u - v| := by
    intro u hu v hv
    have a0 := (hGj 0 (by omega) μ hμ).2 u hu v hv
    have a1 := (hGj 1 le_rfl μ hμ).2 u hu v hv
    have e : (F.G 0 μ u + h * F.G 1 μ u) - (F.G 0 μ v + h * F.G 1 μ v) = (F.G 0 μ u - F.G 0 μ v) + h * (F.G 1 μ u - F.G 1 μ v) := by ring
    rw [e]
    have : |h * (F.G 1 μ u - F.G 1 μ v)| ≤ LG * |u - v| := by
      rw [abs_mul, abs_of_nonneg hpos.le]
      calc h * |F.G 1 μ u - F.G 1 μ v| ≤ 1 * (LG * |u - v|) := mul_le_mul hN1 a1 (abs_nonneg _) zero_le_one
        _ = LG * |u - v| := one_mul _
    have hab := abs_add_le (F.G 0 μ u - F.G 0 μ v) (h * (F.G 1 μ u - F.G 1 μ v))
    have hl : LG * |u - v| ≤ Lj * |u - v| := mul_le_mul_of_nonneg_right (by rw [hLj]; linarith) (abs_nonneg _)
    linarith
  have hBl : ∀ u ∈ Icc 0 F.L, ∀ v ∈ Icc 0 F.L, |(F.B 0 μ u + h * F.B 1 μ u) - (F.B 0 μ v + h * F.B 1 μ v)| ≤ (2 * Lj) * |u - v| := by
    intro u hu v hv
    have a0 := (hBj 0 (by omega) μ hμ).2 u hu v hv
    have a1 := (hBj 1 le_rfl μ hμ).2 u hu v hv
    have e : (F.B 0 μ u + h * F.B 1 μ u) - (F.B 0 μ v + h * F.B 1 μ v) = (F.B 0 μ u - F.B 0 μ v) + h * (F.B 1 μ u - F.B 1 μ v) := by ring
    rw [e]
    have : |h * (F.B 1 μ u - F.B 1 μ v)| ≤ LB * |u - v| := by
      rw [abs_mul, abs_of_nonneg hpos.le]
      calc h * |F.B 1 μ u - F.B 1 μ v| ≤ 1 * (LB * |u - v|) := mul_le_mul hN1 a1 (abs_nonneg _) zero_le_one
        _ = LB * |u - v| := one_mul _
    have hab := abs_add_le (F.B 0 μ u - F.B 0 μ v) (h * (F.B 1 μ u - F.B 1 μ v))
    have hl : LB * |u - v| ≤ Lj * |u - v| := mul_le_mul_of_nonneg_right (by rw [hLj]; linarith) (abs_nonneg _)
    linarith
  -- Lipschitz bound of T^{(h)}(.; X)
  have hLip : ∀ u ∈ Icc 0 F.L, ∀ v ∈ Icc 0 F.L,
      |Tfun F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X u -
        Tfun F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X v| ≤ Lam * |u - v| := by
    intro u hu v hv
    rw [hGfun, hBfun]
    exact tfun_lip F.L_pos (by positivity) hGb hBb hGl hBl hXb hu hv
  -- closeness of T^{(h)} to T at the site
  have hu_n : uNode h n ∈ Icc 0 F.L := by
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hL : h * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
    unfold uNode
    constructor
    · positivity
    · nlinarith
  have hclose := tfun_frozen_close (L := F.L) (G0 := F.G 0 μ) (G1 := F.G 1 μ) (B0 := F.B 0 μ) (B1 := F.B 1 μ) (M := Mj) (MX := MX) (X := X) hpos.le hN1
    (fun u hu => ((hGj 1 le_rfl μ hμ).1 u hu).trans (by rw [hMj]; linarith))
    (fun u hu => ((hBj 1 le_rfl μ hμ).1 u hu).trans (by rw [hMj]; linarith))
    (fun u hu => ((hBj 0 (by omega) μ hμ).1 u hu).trans (by rw [hMj]; linarith)) hXb hu_n
  have hCh : h * Ccl ≤ ε / 2 := by
    calc h * Ccl ≤ ε / (2 * (Ccl + 1)) * Ccl := mul_le_mul_of_nonneg_right hN2 hCcl0
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hε.le hCcl0]
  rw [← hGfun, ← hBfun] at hclose
  have hTh : Tfun F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X (uNode h n) ≤ -(ε / 2) := by
    have := (abs_le.mp hclose).2
    linarith
  have hcol := collar_of_Tneg F.L_pos hhyp hG2 hB2 (by exact lt_of_lt_of_le hband1 hX.1) (by exact lt_of_le_of_lt hX.2 hband2) hLam0
    (by positivity) hLip hu_n hTh
  have e1 : (frozenFamily F Kidx).uMinus (μ, h) X = uMinusS F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X := rfl
  have e2 : (frozenFamily F Kidx).uPlus (μ, h) X = uPlusS F.L ((frozenFamily F Kidx).G 0 (μ, h)) ((frozenFamily F Kidx).B 0 (μ, h)) X := rfl
  rw [e1, e2]
  rcases hcol with h1 | h2
  · left; linarith
  · right; linarith

/-- `step N <= L/(n0 + 1)` forces `n0 <= N`. -/
lemma le_of_step_le {F : SymbolFamily Par} {n0 N : ℕ} (h : F.step N ≤ F.L / ((n0 : ℝ) + 1)) : n0 ≤ N := by
  have hL : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  rw [le_div_iff₀ (by positivity)] at h
  have : ((n0 : ℝ) + 1) ≤ (N : ℝ) + 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [F.L_pos]
  exact_mod_cast (by linarith : (n0 : ℝ) ≤ N)

/-- **`ThmAii`, relative clause, bulk case** (paper: "The relative statement", *Bulk case*): for the eigenvalues `X_k` that fall in a bulk block (first case of `def:tha-Psihat`), `V_{k,n} <= C_eps |hat Psi_{k,n}|`
at every site with `T(u_n; X_k) <= -eps`.  From the collar clause of `PropThaW` (`hW`, the fourth conjunct: `bulkEnv <= C_delta |bulkVec|` on the `delta`-collars) and `bulk_relative_collar`
(`T <= -eps` puts `u_n` in a collar, uniformly).  Premises: `PropThaW` for every block (the collar clause only is used; its first conjuncts are *not*), `StdAssump` of the frozen family at index `m/2`
(the premise of `PropThaW`) and at `Kidx` (for the geometry), the chart data `CI`. -/
theorem thmAii_bulk_relative {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m) (hK : IsCompact K) (hD : DM F K 1)
    (hstdM : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r)
    (hW : ∀ ν, PropThaW (frozenFamily F Kidx) (paramSet K t0) (CI.lo ν) (CI.hi ν) m U V (CI.bulkL ν) (CI.bulkR ν)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cε hε' : ℝ, 0 < hε' ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε' → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε →
            envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n| := by
  obtain ⟨rK, hrK⟩ := hstdK
  obtain ⟨rM, hrM⟩ := hstdM
  obtain ⟨δ, h1, hδ, hh1, hcol⟩ := bulk_relative_collar hK hD hrK (fun p hp => ⟨(CI.cover p hp).1, (CI.cover p hp).2.2.1⟩) hε
  -- the collar clause of PropThaW, per block
  have hcl : ∀ ν, ∃ Cδ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ paramSet K t0, ∀ X ∈ Icc (CI.lo ν) (CI.hi ν), ∀ N : ℕ,
      max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ N → (frozenFamily F Kidx).step N ≤ h0 →
      ∀ n ∈ rowsOf N, (uNode ((frozenFamily F Kidx).step N) n ≤ (frozenFamily F Kidx).uMinus p X - δ ∨
        (frozenFamily F Kidx).uPlus p X + δ ≤ uNode ((frozenFamily F Kidx).step N) n) →
        bulkEnv (CI.bulkL ν) (CI.bulkR ν) p X N n ≤ Cδ * |bulkVec (CI.bulkL ν) (CI.bulkR ν) p X N n| := by
    intro ν
    obtain ⟨-, -, -, hcoll⟩ := hW ν hm (CI.overlap_match ν) rM hrM
    obtain ⟨Cδ, h0, hh0, H⟩ := hcoll δ hδ
    exact ⟨Cδ, h0, hh0, H⟩
  choose Cd h0 hh0 hH using hcl
  set Csum : ℝ := ∑ ν, |Cd ν| with hCsum
  set n0 : ℕ := ∑ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 with hn0
  have hn0le : ∀ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ n0 :=
    fun ν => Finset.single_le_sum (f := fun ν => max (CI.bulkL ν).N0 (CI.bulkR ν).N0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
  by_cases hnb : Nonempty (Fin CI.nb)
  · obtain ⟨ν0⟩ := hnb
    haveI : Nonempty (Fin CI.nb) := ⟨ν0⟩
    have hminpos : ∃ hm0 : ℝ, 0 < hm0 ∧ ∀ ν, hm0 ≤ h0 ν := by
      obtain ⟨i, hi⟩ := Finite.exists_min h0
      exact ⟨h0 i, hh0 i, hi⟩
    obtain ⟨hm0, hm0pos, hm0le⟩ := hminpos
    refine ⟨Csum, min (min h1 hm0) (F.L / ((n0 : ℝ) + 1)), lt_min (lt_min hh1 hm0pos) (div_pos F.L_pos (by positivity)), ?_⟩
    intro μ hμ N hN hNt X Um hE k hk n hn hT
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN2 : F.step N ≤ hm0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hN3 : F.step N ≤ F.L / ((n0 : ℝ) + 1) := hN.trans (min_le_right _ _)
    have hn0N : n0 ≤ N := le_of_step_le hN3
    have hd : ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν := hk
    have hspec := Classical.choose_spec hd
    set ν := Classical.choose hd with hν
    have hXJ : X k ∈ Icc CI.Jlo CI.Jhi := by
      obtain ⟨hb1, -, hb3⟩ := CI.blocks_in_J ν
      exact ⟨hb1.trans hspec.1, hspec.2.trans hb3⟩
    have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
    have hco := hcol μ hμ N hN1 hNt (X k) hXJ n hn hT
    have hbe := hH ν (μ, F.step N) hp (X k) hspec (N) (le_trans (hn0le ν) hn0N) ((hN2.trans (hm0le ν)))
      n hn hco
    have e1 : envVec CI μ N (X k) n = bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (X k) N n := by
      unfold envVec; rw [dite_eq_left hd]
    have e2 : psiHatVec CI μ N (X k) n = bulkVec (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (X k) N n := by
      unfold psiHatVec; rw [dite_eq_left hd]
    rw [e1, e2]
    refine hbe.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun ν => |Cd ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ν))
  · refine ⟨0, 1, one_pos, ?_⟩
    intro μ hμ N hN hNt X Um hE k hk
    obtain ⟨ν, -⟩ := hk
    exact (hnb ⟨ν⟩).elim

/-! ### The assembly of `ThmAii` from its three cases -/

/-- The two clauses of the absolute statement of `ThmAii` for one eigenvalue (constant `C`). -/
def AiiAbs {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (C : ℝ) (μ : Par) (N : ℕ)
    (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) : Prop :=
  (∀ n ∈ rowsOf N, |eigVec Um k n - psiHatVec CI μ N (X k) n| ≤ C * F.step N ^ m * envVec CI μ N (X k) n) ∧
    ∑ n ∈ rowsOf N, envVec CI μ N (X k) n ^ 2 ≤ C

lemma AiiAbs.mono {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    {CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC} {C C' : ℝ} (hC : C ≤ C') {μ : Par} {N : ℕ}
    {X : Fin (N + 1) → ℝ} {Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {k : Fin (N + 1)}
    (hnn : ∀ n ∈ rowsOf N, 0 ≤ envVec CI μ N (X k) n) (hpos : 0 < F.step N) (h : AiiAbs CI C μ N X Um k) : AiiAbs CI C' μ N X Um k := by
  refine ⟨fun n hn => (h.1 n hn).trans ?_, h.2.trans hC⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg hpos.le _)) (hnn n hn)

/-- **`ThmAii` modulo its three cases.**  The eigenvalue falls in a bulk block, or above `J_hi` within the window of the upper soft chart, or below within the window of the lower one
(`spectrumCovered`, proved); each case is a premise (`hB`: `PropThaW` with the envelope sum; `hU`: `PropThaW2` at `Cs0` of `stepZero`; `hL`: the same through the reversal `NegTransport`), with
constants combined by `max`; the envelopes are nonnegative (`hnn`: `softEnv_nonneg`, `bulkEnv_nonneg_rows`).  The relative clause is assembled the same way from its three cases (`rB`, `rU`, `rL`). -/
theorem thmAii_of_cases {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC)
    (hnn : ∃ hn : ℝ, 0 < hn ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hn → F.step N ≤ t0 → ∀ x : ℝ, ∀ n ∈ rowsOf N, 0 ≤ envVec CI μ N x n)
    (hB : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → AiiAbs CI C μ N X Um k)
    (hU : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → AiiAbs CI C μ N X Um k)
    (hL : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → AiiAbs CI C μ N X Um k)
    (hcov : SpectrumCovered CI) (hKidx : Kidx = (m + 1) / 2) (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K (2 * Kidx + 1))
    (rB : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|)
    (rU : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|)
    (rL : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|) :
    (∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∀ n ∈ rowsOf N, |eigVec Um k n - psiHatVec CI μ N (X k) n| ≤ C * F.step N ^ m * envVec CI μ N (X k) n) ∧
          ∑ n ∈ rowsOf N, envVec CI μ N (X k) n ^ 2 ≤ C) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε →
            envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|) := by
  have hDc : DM F K (2 * Kidx + 1) := hD
  obtain ⟨hc0, hc0p, hcover⟩ := hcov hKidx hK hH hDc
  refine ⟨?_, fun ε hε => ?_⟩
  · obtain ⟨Cb, hb, hbp, Hb⟩ := hB
    obtain ⟨Cu, hu, hup, Hu⟩ := hU
    obtain ⟨Cl, hl, hlp, Hl⟩ := hL
    obtain ⟨hn0, hn0p, hnn'⟩ := hnn
    refine ⟨max (max Cb Cu) Cl, min (min (min hb hu) (min hl hc0)) hn0, lt_min (lt_min (lt_min hbp hup) (lt_min hlp hc0p)) hn0p, ?_⟩
    intro μ hμ N hN hNt X Um hE k
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have h1 : F.step N ≤ hb := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have h2 : F.step N ≤ hu := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    have h3 : F.step N ≤ hl := hN.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have h4 : F.step N ≤ hc0 := hN.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have h5 : F.step N ≤ t0 := hNt
    have hnnk := hnn' μ hμ N (hN.trans (min_le_right _ _)) h5 (X k)
    have key : AiiAbs CI (max (max Cb Cu) Cl) μ N X Um k := by
      rcases hcover μ hμ N h4 h5 X Um hE k with hb' | hu' | hl'
      · exact (Hb μ hμ N h1 h5 X Um hE k hb').mono ((le_max_left _ _).trans (le_max_left _ _)) hnnk hpos
      · exact (Hu μ hμ N h2 h5 X Um hE k hu'.1 hu'.2.1 hu'.2.2).mono (((le_max_right _ _).trans (le_max_left _ _))) hnnk hpos
      · exact (Hl μ hμ N h3 h5 X Um hE k hl'.1 hl'.2.1 hl'.2.2).mono (le_max_right _ _) hnnk hpos
    exact key
  · obtain ⟨Cb, hb, hbp, Hb⟩ := rB ε hε
    obtain ⟨Cu, hu, hup, Hu⟩ := rU ε hε
    obtain ⟨Cl, hl, hlp, Hl⟩ := rL ε hε
    refine ⟨max (max Cb Cu) Cl, min (min hb hu) (min hl hc0), lt_min (lt_min hbp hup) (lt_min hlp hc0p), ?_⟩
    intro μ hμ N hN hNt X Um hE k n hn hT
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have h1 : F.step N ≤ hb := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : F.step N ≤ hu := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : F.step N ≤ hl := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h4 : F.step N ≤ hc0 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h5 : F.step N ≤ t0 := hNt
    have habs := abs_nonneg (psiHatVec CI μ N (X k) n)
    have hmono : ∀ C : ℝ, envVec CI μ N (X k) n ≤ C * |psiHatVec CI μ N (X k) n| → C ≤ max (max Cb Cu) Cl →
        envVec CI μ N (X k) n ≤ max (max Cb Cu) Cl * |psiHatVec CI μ N (X k) n| := fun C hC hCm =>
      hC.trans (mul_le_mul_of_nonneg_right hCm habs)
    rcases hcover μ hμ N h4 h5 X Um hE k with hb' | hu' | hl'
    · exact hmono Cb (Hb μ hμ N h1 h5 X Um hE k hb' n hn hT) ((le_max_left _ _).trans (le_max_left _ _))
    · exact hmono Cu (Hu μ hμ N h2 h5 X Um hE k hu'.1 hu'.2.1 hu'.2.2 n hn hT) ((le_max_right _ _).trans (le_max_left _ _))
    · exact hmono Cl (Hl μ hμ N h3 h5 X Um hE k hl'.1 hl'.2.1 hl'.2.2 n hn hT) (le_max_right _ _)

/-- **`ThmAi` from `ThmSmoSpec`** (thm:A (i) is the existence part of thm:smo-spec). -/
theorem thmAi_of_smoSpec {F : SymbolFamily Par} {K : Set Par} {M Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    {CI : ChartInputs (truncFamily F M) K Kidx t0 (max M 1) (2 * Kidx) U V cPC CPC}
    {PI : ∀ ν, BulkPhaseInputs (frozenFamily (truncFamily F M) Kidx) (paramSet K t0) K t0 (CI.lo ν) (CI.hi ν) M U V (CI.bulkL ν) (CI.bulkR ν)}
    (h : ThmSmoSpec F K M Kidx t0 U V cPC CPC CI PI) (hKidx : Kidx = (M + 1) / 2) : ThmAi F K M :=
  (h hKidx).1

/-- **`ThmAii` modulo its cases, in the frozen form**: `thmAii_of_cases` with `spectrumCovered CI` (proved) plugged in, under the hypotheses of `ThmAii`. -/
theorem thmAii_of_cases' {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC)
    (hnn : ∃ hn : ℝ, 0 < hn ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hn → F.step N ≤ t0 → ∀ x : ℝ, ∀ n ∈ rowsOf N, 0 ≤ envVec CI μ N x n)
    (hB : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → AiiAbs CI C μ N X Um k)
    (hU : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → AiiAbs CI C μ N X Um k)
    (hL : ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → AiiAbs CI C μ N X Um k)
    (rB : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|)
    (rU : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|)
    (rL : ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n|) :
    ThmAii F K m Kidx t0 U V cPC CPC CI := by
  intro hm1 hKidx hK hH hD
  have hDc : DM F K (2 * Kidx + 1) := by rw [hKidx]; exact hD
  exact thmAii_of_cases CI hnn hB hU hL (spectrumCovered CI) hKidx hK hH hDc rB rU rL

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_relative_collar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_relative_collar

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAii_bulk_relative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAii_bulk_relative

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAii_of_cases'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAii_of_cases'

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_smoSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAi_of_smoSpec

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.collar_of_Tneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.collar_of_Tneg

end FormalResearch.JacobiEigenvectors.TheoremA

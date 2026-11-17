module

public import FormalResearch.Special.DiscreteAirySecondPair
public import FormalResearch.Special.DiscreteAirySecondJets

/-!
# Second-order Airy parametrix, part 8: the `q`-level link data (Q2)

For smooth data `ζ, A, A₂, g, p, q₁` on an open `U ⊇ J` (`J` compact) this module builds the `LinkData` of
`DiscreteAirySecondLink` for **both** links `±h` (`LinkData` at `hh = t³`, `t` and at `hh = -t³`, `-t`), uniformly over the
parameter set `{(q, t) : q ∈ J, 0 < |t| ≤ 1, |t|³ ≤ τ}`:

* `z₀..z₃ = ζ, ζ', ζ'', ζ'''` at `q`, with the remainder `e` of `(ζ(q+h) - ζ(q))/h = z₁ + h z₂/2 + h² z₃/6 + e` (`ζ ∈ C⁴`);
* `G = a(q + h/2) P(q + h)` with `a = A + h² A₂`, `P = g + h² p` (jets `G₀ = A g`, `G₁ = (A' g)/2 + A g'`,
  `G₂ = A'' g/8 + A' g'/2 + A g''/2 + A₂ g + A p`), `A, g ∈ C³`, `A₂, p ∈ C¹`;
* `H = a(q + h/2) q₁(q + h)` (jets `H₀ = A q₁`, `H₁ = A' q₁/2 + A q₁'`), remainder `O(h²)`, `q₁ ∈ C³`.

`Airy2Data.linkData` is the single statement; the constants `τ, Z₀, S, B` are existential.  The assembly with the central
terms (eikonal, transport, `q₁`-residual) is in `DiscreteAirySecondAssembly`.  **Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-! ### the jets of the data -/

/-- `G₀ = A g`. -/
noncomputable def a2G0 (A g : ℝ → ℝ) (q : ℝ) : ℝ := A q * g q
/-- `G₁ = A' g/2 + A g'`. -/
noncomputable def a2G1 (A g : ℝ → ℝ) (q : ℝ) : ℝ := deriv A q * g q / 2 + A q * deriv g q
/-- `G₂ = A'' g/8 + A' g'/2 + A g''/2 + A₂ g + A p`. -/
noncomputable def a2G2 (A A2 g p : ℝ → ℝ) (q : ℝ) : ℝ :=
  deriv (deriv A) q * g q / 8 + deriv A q * deriv g q / 2 + A q * (deriv (deriv g) q / 2) + A2 q * g q + A q * p q
/-- `H₀ = A q₁`. -/
noncomputable def a2H0 (A q1 : ℝ → ℝ) (q : ℝ) : ℝ := A q * q1 q
/-- `H₁ = A' q₁/2 + A q₁'`. -/
noncomputable def a2H1 (A q1 : ℝ → ℝ) (q : ℝ) : ℝ := deriv A q * q1 q / 2 + A q * deriv q1 q
/-- The link amplitude `G(q; h) = (A + h² A₂)(q + h/2) · (g + h² p)(q + h)`. -/
noncomputable def a2G (A A2 g p : ℝ → ℝ) (q h : ℝ) : ℝ :=
  (A (q + h / 2) + h ^ 2 * A2 (q + h / 2)) * (g (q + h) + h ^ 2 * p (q + h))
/-- The link amplitude `H(q; h) = (A + h² A₂)(q + h/2) · q₁(q + h)`. -/
noncomputable def a2H (A A2 q1 : ℝ → ℝ) (q h : ℝ) : ℝ := (A (q + h / 2) + h ^ 2 * A2 (q + h / 2)) * q1 (q + h)
/-- The remainder `e` in `(ζ(q+h) - ζ(q))/h = ζ' + h ζ''/2 + h² ζ'''/6 + e`. -/
noncomputable def a2e (ζ : ℝ → ℝ) (q h : ℝ) : ℝ :=
  (ζ (q + h) - ζ q) / h - (deriv ζ q + h * deriv (deriv ζ) q / 2 + h ^ 2 * deriv (deriv (deriv ζ)) q / 6)

/-- The regularity hypotheses of the second-order construction. -/
structure Airy2Data (U : Set ℝ) (ζ A A2 g p q1 : ℝ → ℝ) : Prop where
  hU : IsOpen U
  hζ : ContDiffOn ℝ 4 ζ U
  hA : ContDiffOn ℝ 3 A U
  hA2 : ContDiffOn ℝ 1 A2 U
  hg : ContDiffOn ℝ 3 g U
  hp : ContDiffOn ℝ 1 p U
  hq1 : ContDiffOn ℝ 3 q1 U

section Calc

variable {α : Type*} {D : α → Prop} {hh : α → ℝ}

/-- `hh² f(q + c hh)` for `f ∈ C¹`: the `Ex3` jet `(0, 0, f(q))`. -/
theorem Ex3.of_h2lip {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {α : Type} (D : α → Prop) (hh q : α → ℝ), (∀ a, D a → q a ∈ J) →
      (∀ a, D a → |c| * |hh a| ≤ δ) →
      Ex3 D hh (fun a => hh a ^ 2 * f (q a + c * hh a)) (fun _ => 0) (fun _ => 0) (fun a => f (q a)) := by
  obtain ⟨δ, hδ, H⟩ := SOB.lip1 hU hf hJ hJU c
  refine ⟨δ, hδ, fun {α} D hh q hq hc => ?_⟩
  obtain ⟨h1, h2⟩ := H D hh q hq hc
  exact ⟨h1.congr fun a _ => by ring, SOB.const 0, SOB.const 0, h2⟩

end Calc

/-- **Q2: the link data of both links, uniformly on `J × {0 < |t|³ ≤ τ}`.** -/
theorem Airy2Data.linkData {U J : Set ℝ} {ζ A A2 g p q1 : ℝ → ℝ} (hD : Airy2Data U ζ A A2 g p q1)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ τ Z0 S B : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 0 ≤ Z0 ∧ 0 ≤ S ∧ 0 ≤ B ∧
      ∀ {α : Type} (D : α → Prop) (hh t q : α → ℝ), (∀ a, D a → q a ∈ J) →
        (∀ a, D a → hh a = t a ^ 3 ∧ t a ≠ 0 ∧ |t a| ≤ 1 ∧ |hh a| ≤ τ) →
        LinkData D hh t (fun a => ζ (q a)) (fun a => deriv ζ (q a)) (fun a => deriv (deriv ζ) (q a))
          (fun a => deriv (deriv (deriv ζ)) (q a)) (fun a => a2e ζ (q a) (hh a))
          (fun a => a2G0 A g (q a)) (fun a => a2G1 A g (q a)) (fun a => a2G2 A A2 g p (q a))
          (fun a => a2G A A2 g p (q a) (hh a) -
            (a2G0 A g (q a) + hh a * a2G1 A g (q a) + hh a ^ 2 * a2G2 A A2 g p (q a)))
          (fun a => a2H0 A q1 (q a)) (fun a => a2H1 A q1 (q a))
          (fun a => a2H A A2 q1 (q a) (hh a) - (a2H0 A q1 (q a) + hh a * a2H1 A q1 (q a))) Z0 S B := by
  obtain ⟨M0, M1, M2, M3, M4, δζ, hM0, hM1, hM2, hM3, hM4, hδζ, hjζ⟩ := sj_jet4 hD.hU hD.hζ hJ hJU
  obtain ⟨δA, hδA, HA⟩ := Ex3.of_q3 hD.hU hD.hA hJ hJU (1 / 2)
  obtain ⟨δg, hδg, Hg⟩ := Ex3.of_q3 hD.hU hD.hg hJ hJU 1
  obtain ⟨δq, hδq, Hq⟩ := Ex3.of_q3 hD.hU hD.hq1 hJ hJU 1
  obtain ⟨δA2, hδA2, HA2⟩ := Ex3.of_h2lip hD.hU hD.hA2 hJ hJU (1 / 2)
  obtain ⟨δp, hδp, Hp⟩ := Ex3.of_h2lip hD.hU hD.hp hJ hJU 1
  set τ : ℝ := min 1 (min δζ (min (2 * δA) (min δg (min δq (min (2 * δA2) δp))))) with hτ
  have hτ0 : 0 < τ := by
    refine lt_min one_pos (lt_min hδζ (lt_min (by linarith) (lt_min hδg (lt_min hδq (lt_min (by linarith) hδp)))))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτζ : τ ≤ δζ := (min_le_right _ _).trans (min_le_left _ _)
  have hτA : τ ≤ 2 * δA := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτg : τ ≤ δg := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hτq : τ ≤ δq := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hτA2 : τ ≤ 2 * δA2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hτp : τ ≤ δp := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨τ, M0, M1 + M2 + M3 + M4, M2 + M3, hτ0, hτ1, hM0, by positivity, by positivity, ?_⟩
  intro α D hh t q hq hhyp
  have hh1 : ∀ a, D a → |hh a| ≤ 1 := fun a ha => ((hhyp a ha).2.2.2).trans hτ1
  have hhτ : ∀ a, D a → |hh a| ≤ τ := fun a ha => (hhyp a ha).2.2.2
  have hh0 : ∀ a, D a → hh a ≠ 0 := fun a ha => by
    rw [(hhyp a ha).1]; exact pow_ne_zero 3 (hhyp a ha).2.1
  -- the jets of the amplitudes
  have eA := HA D hh q hq (fun a ha => by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [hhτ a ha])
  have eg := Hg D hh q hq (fun a ha => by rw [abs_one]; linarith [hhτ a ha])
  have eq := Hq D hh q hq (fun a ha => by rw [abs_one]; linarith [hhτ a ha])
  have eA2 := HA2 D hh q hq (fun a ha => by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [hhτ a ha])
  have ep := Hp D hh q hq (fun a ha => by rw [abs_one]; linarith [hhτ a ha])
  have fa := eA.add eA2
  have fg := eg.add ep
  have hG : Ex3 D hh (fun a => a2G A A2 g p (q a) (hh a)) (fun a => a2G0 A g (q a))
      (fun a => a2G1 A g (q a)) (fun a => a2G2 A A2 g p (q a)) := by
    refine (Ex3.mul hh1 fa fg).congr (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_)
    · unfold a2G; congr 2 <;> ring_nf
    · unfold a2G0; ring
    · unfold a2G1; ring
    · unfold a2G2; ring
  have hH : Ex3 D hh (fun a => a2H A A2 q1 (q a) (hh a)) (fun a => a2H0 A q1 (q a))
      (fun a => a2H1 A q1 (q a))
      (fun a => (1 / 2) * deriv A (q a) * deriv q1 (q a) + (1 / 2) ^ 2 * deriv (deriv A) (q a) / 2 * q1 (q a) +
        A (q a) * (1 ^ 2 * deriv (deriv q1) (q a) / 2) + A2 (q a) * q1 (q a)) := by
    refine (Ex3.mul hh1 fa eq).congr (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_) (fun a _ => ?_)
    · unfold a2H; congr 2 <;> ring_nf
    · unfold a2H0; ring
    · unfold a2H1; ring
    · ring
  -- remainder of `ζ`
  have heb : ∀ a, D a → |a2e ζ (q a) (hh a)| ≤ M4 * |hh a| ^ 3 := by
    intro a ha
    have hq' := (hjζ (q a) (hq a ha)).2.2.2.2 (hh a) ((hhτ a ha).trans hτζ)
    have hh0' := hh0 a ha
    have hpos : 0 < |hh a| := abs_pos.2 hh0'
    have e : a2e ζ (q a) (hh a) = (ζ (q a + hh a) - (ζ (q a) + deriv ζ (q a) * hh a +
        deriv (deriv ζ) (q a) * hh a ^ 2 / 2 + deriv (deriv (deriv ζ)) (q a) * hh a ^ 3 / 6)) / hh a := by
      unfold a2e; field_simp; ring
    rw [e, abs_div, div_le_iff₀ hpos]
    calc _ ≤ M4 * |hh a| ^ 4 := hq'
      _ = M4 * |hh a| ^ 3 * |hh a| := by ring
  have he : SOB D hh 3 (fun a => a2e ζ (q a) (hh a)) := ⟨M4, hM4, heb⟩
  refine ⟨hh1, fun a ha => (hhyp a ha).1, fun a ha => (hhyp a ha).2.1, fun a ha => (hhyp a ha).2.2.1, hM0,
    by positivity, fun a ha => (hjζ (q a) (hq a ha)).1, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, he,
    fun a ha => ?_, hG.2.1, hG.2.2.1, hG.2.2.2, hG.1, hH.2.1, hH.2.2.1, ?_⟩
  · have := (hjζ (q a) (hq a ha)).2.1
    show |deriv ζ (q a)| ≤ M1 + M2 + M3 + M4
    linarith
  · have := (hjζ (q a) (hq a ha)).2.2.1
    show |deriv (deriv ζ) (q a)| ≤ M2 + M3
    linarith
  · have := (hjζ (q a) (hq a ha)).2.2.2.1
    show |deriv (deriv (deriv ζ)) (q a)| ≤ M2 + M3
    linarith
  · obtain ⟨-, b1, b2, b3, -⟩ := hjζ (q a) (hq a ha)
    have hb := hh1 a ha
    have h0 := abs_nonneg (hh a)
    have heb' : |a2e ζ (q a) (hh a)| ≤ M4 := by
      have := heb a ha
      have h3 : |hh a| ^ 3 ≤ 1 := pow_le_one₀ h0 hb
      nlinarith
    have t2 : |hh a * deriv (deriv ζ) (q a) / 2| ≤ M2 := by
      rw [abs_div, abs_mul, abs_two]
      have : |hh a| * |deriv (deriv ζ) (q a)| ≤ 1 * M2 := mul_le_mul hb b2 (abs_nonneg _) zero_le_one
      linarith
    have t3 : |hh a ^ 2 * deriv (deriv (deriv ζ)) (q a) / 6| ≤ M3 := by
      rw [abs_div, abs_mul, abs_pow]
      have h2 : |hh a| ^ 2 ≤ 1 := pow_le_one₀ h0 hb
      have : |hh a| ^ 2 * |deriv (deriv (deriv ζ)) (q a)| ≤ 1 * M3 :=
        mul_le_mul h2 b3 (abs_nonneg _) zero_le_one
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      linarith
    show |deriv ζ (q a) + (hh a * deriv (deriv ζ) (q a) / 2 + hh a ^ 2 * deriv (deriv (deriv ζ)) (q a) / 6 +
      a2e ζ (q a) (hh a))| ≤ M1 + M2 + M3 + M4
    have u1 := abs_add_le (deriv ζ (q a)) (hh a * deriv (deriv ζ) (q a) / 2 +
      hh a ^ 2 * deriv (deriv (deriv ζ)) (q a) / 6 + a2e ζ (q a) (hh a))
    have u2 := abs_add_le (hh a * deriv (deriv ζ) (q a) / 2 + hh a ^ 2 * deriv (deriv (deriv ζ)) (q a) / 6)
      (a2e ζ (q a) (hh a))
    have u3 := abs_add_le (hh a * deriv (deriv ζ) (q a) / 2) (hh a ^ 2 * deriv (deriv (deriv ζ)) (q a) / 6)
    linarith
  · obtain ⟨r3, -, -, c2b⟩ := hH
    have := (r3.mono hh1 (by norm_num : 2 ≤ 3)).add (((SOB.hh_pow (D := D) (hh := hh) 2).mul c2b))
    exact this.congr fun a _ => by ring

/-- info: 'FormalResearch.Special.Airy2Data.linkData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.Airy2Data.linkData

end FormalResearch.Special

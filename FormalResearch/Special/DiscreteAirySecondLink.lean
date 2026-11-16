module

public import FormalResearch.Special.DiscreteAirySecondJet

/-!
# Second-order Airy parametrix, part 4: expansion of one signed link to order `h²`

For the paper-form parametrix `ψ̃ = P χ(X) + h^{1/3} Q χ'(X)`, `Q = h q₁` (`χ` any solution of `χ'' = x χ`), the defect is
`χ 𝔄 + h^{1/3} χ' 𝔅` with
`𝔄 = Σ_± a_± [P_± C(s_±) + Q_± C'(s_±)] - c P`,  `𝔅 = Σ_± a_± [P_± S(s_±) + Q_± S'(s_±)] - c Q`.
The two links `±` are the *same function* at `t` and `-t` (parity of the scaled shift functions is definitional:
`Cs z t (-s) = Cs z (-t) s`, `Ss z t (-s) = - Ss z (-t) s`, `Cs1 z t (-s) = - Cs1 z (-t) s`, `Ss1 z t (-s) = Ss1 z (-t) s`), so only
**one** link has to be expanded, to order `h²` with `O(|h|³)` remainder uniformly in the sign of `t`.

With `h = hh = t³`, `s = z₁ + δ`, `δ = h z₂/2 + h² z₃/6 + e` (`e = O(h³)`), `G = G₀ + hG₁ + h²G₂ + γ`,
`H = H₀ + hH₁ + η` (`η = O(h²)`) this module proves

* `LinkData.exA`: `G · Cs(z₀, t, s) + h H · Cs'(z₀, t, s)` has the expansion `LA0 + h LA1 + h² LA2 + O(h³)`;
* `LinkData.exS`: `G · Ss(z₀, t, s) + h H · Ss'(z₀, t, s)` has the expansion `LS0 + h LS1 + h² LS2 + O(h³)`,

with explicit coefficients (`lkA1`, `lkA2`, `lkS1`, `lkS2` below), in terms of the closed forms `E, O, C₂, A, B, S₂` and their
`s`-derivatives at `(z₀, z₁)`.  **Claim class: proved.**
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-! ### two more derivative identities -/

/-- `d/ds (ζ O + s E) = ζ O₁ + E + s E₁`. -/
lemma apu2_hasDerivAt_OE (z s : ℝ) :
    HasDerivAt (fun x => z * apuO z x + x * apuE z x) (z * apuO1 z s + (apuE z s + s * apuE1 z s)) s := by
  have := ((apu_hasDerivAt_O z s).const_mul z).add ((hasDerivAt_id s).mul (apu_hasDerivAt_E z s))
  refine this.congr_deriv ?_
  simp

/-- `d/ds (ζ B + s A) = ζ B₁ + A + s E`. -/
lemma apu2_hasDerivAt_BA (z s : ℝ) :
    HasDerivAt (fun x => z * apuB z x + x * apuA z x) (z * apuB1 z s + (apuA z s + s * apuE z s)) s := by
  have := ((apu_hasDerivAt_B z s).const_mul z).add ((hasDerivAt_id s).mul (apu_hasDerivAt_A z s))
  refine this.congr_deriv ?_
  simp

/-- `d/ds (ζ E) = ζ E₁`. -/
lemma apu2_hasDerivAt_zE (z s : ℝ) : HasDerivAt (fun x => z * apuE z x) (z * apuE1 z s) s :=
  (apu_hasDerivAt_E z s).const_mul z

/-- `d/ds (ζ E₁) = ζ (ζ E)`. -/
lemma apu2_hasDerivAt_zE1 (z s : ℝ) : HasDerivAt (fun x => z * apuE1 z x) (z * (z * apuE z s)) s :=
  (apu_hasDerivAt_E1 z s).const_mul z

/-- `d/ds (ζ C₂ + s O) = ζ C₂₁ + O + s O₁`. -/
lemma apu2_hasDerivAt_C2O (z s : ℝ) :
    HasDerivAt (fun x => z * apuC2 z x + x * apuO z x) (z * apuC21 z s + (apuO z s + s * apuO1 z s)) s := by
  have := ((apu2_hasDerivAt_C2 z s).const_mul z).add ((hasDerivAt_id s).mul (apu_hasDerivAt_O z s))
  refine this.congr_deriv ?_
  simp

/-- `d/ds (ζ S₂ + s B) = ζ S₂₁ + B + s B₁`. -/
lemma apu2_hasDerivAt_S2B (z s : ℝ) :
    HasDerivAt (fun x => z * apuS2 z x + x * apuB z x) (z * apuS21 z s + (apuB z s + s * apuB1 z s)) s := by
  have := ((apu2_hasDerivAt_S2 z s).const_mul z).add ((hasDerivAt_id s).mul (apu_hasDerivAt_B z s))
  refine this.congr_deriv ?_
  simp

/-- Uniform bounds for the closed forms (`E, E₁, O, O₁, A, B, B₁, C₂, C₂₁, S₂, S₂₁`). -/
lemma apu2_bnd (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z s : ℝ, |z| ≤ Z0 → |s| ≤ S →
      |apuE z s| ≤ M ∧ |apuE1 z s| ≤ M ∧ |apuO z s| ≤ M ∧ |apuO1 z s| ≤ M ∧ |apuA z s| ≤ M ∧
      |apuB z s| ≤ M ∧ |apuB1 z s| ≤ M ∧ |apuC2 z s| ≤ M ∧ |apuC21 z s| ≤ M ∧ |apuS2 z s| ≤ M ∧
      |apuS21 z s| ≤ M := by
  obtain ⟨M1, hM10, hM1⟩ := apu_bounds Z0 S hZ0 hS
  obtain ⟨M2, hM20, hM2⟩ := apu2_bounds Z0 S hZ0 hS
  refine ⟨M1 + M2, by positivity, fun z s hz hs => ?_⟩
  obtain ⟨e0, e1, o0, o1, a0, b0, b1⟩ := hM1 z s hz hs
  obtain ⟨c0, c1, s0, s1⟩ := hM2 z s hz hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma sj_b1 {z x Z0 M : ℝ} (hz : |z| ≤ Z0) (hx : |x| ≤ M) (hZ : 0 ≤ Z0) : |z * x| ≤ Z0 * M := by
  rw [abs_mul]; exact mul_le_mul hz hx (abs_nonneg _) hZ

lemma sj_b2 {z s x y Z0 S M : ℝ} (hz : |z| ≤ Z0) (hs : |s| ≤ S) (hx : |x| ≤ M) (hy : |y| ≤ M) (hZ : 0 ≤ Z0)
    (hS : 0 ≤ S) : |z * x + s * y| ≤ Z0 * M + S * M :=
  (abs_add_le _ _).trans (add_le_add (sj_b1 hz hx hZ) (sj_b1 hs hy hS))

lemma sj_b3 {z s x y w Z0 S M : ℝ} (hz : |z| ≤ Z0) (hs : |s| ≤ S) (hx : |x| ≤ M) (hy : |y| ≤ M) (hw : |w| ≤ M)
    (hZ : 0 ≤ Z0) (hS : 0 ≤ S) : |z * x + (y + s * w)| ≤ Z0 * M + (M + S * M) :=
  (abs_add_le _ _).trans (add_le_add (sj_b1 hz hx hZ) ((abs_add_le _ _).trans (add_le_add hy (sj_b1 hs hw hS))))

/-! ### the expansion coefficients -/

noncomputable def lkcs1 (z0 z1 z2 : ℝ) : ℝ := apuE1 z0 z1 * (z2 / 2) + apuO z0 z1
noncomputable def lkcs2 (z0 z1 z2 z3 : ℝ) : ℝ :=
  apuE1 z0 z1 * (z3 / 6) + z0 * apuE z0 z1 * (z2 / 2) ^ 2 / 2 + apuO1 z0 z1 * (z2 / 2) + apuC2 z0 z1
noncomputable def lkds1 (z0 z1 z2 : ℝ) : ℝ := z0 * apuE z0 z1 * (z2 / 2) + apuO1 z0 z1
noncomputable def lkds2 (z0 z1 z2 z3 : ℝ) : ℝ :=
  z0 * apuE z0 z1 * (z3 / 6) + z0 * apuE1 z0 z1 * (z2 / 2) ^ 2 / 2 +
    (z0 * apuO z0 z1 + z1 * apuE z0 z1) * (z2 / 2) + apuC21 z0 z1
noncomputable def lkss1 (z0 z1 z2 : ℝ) : ℝ := apuE z0 z1 * (z2 / 2) + apuB z0 z1
noncomputable def lkss2 (z0 z1 z2 z3 : ℝ) : ℝ :=
  apuE z0 z1 * (z3 / 6) + apuE1 z0 z1 * (z2 / 2) ^ 2 / 2 + apuB1 z0 z1 * (z2 / 2) + apuS2 z0 z1
noncomputable def lkus1 (z0 z1 z2 : ℝ) : ℝ := apuE1 z0 z1 * (z2 / 2) + apuB1 z0 z1
noncomputable def lkus2 (z0 z1 z2 z3 : ℝ) : ℝ :=
  apuE1 z0 z1 * (z3 / 6) + z0 * apuE z0 z1 * (z2 / 2) ^ 2 / 2 +
    (z0 * apuB z0 z1 + z1 * apuA z0 z1) * (z2 / 2) + apuS21 z0 z1

/-- `h⁰` coefficient of the `𝔄`-link. -/
noncomputable def lkA0 (z0 z1 G0 : ℝ) : ℝ := G0 * apuE z0 z1
/-- `h¹` coefficient of the `𝔄`-link. -/
noncomputable def lkA1 (z0 z1 z2 G0 G1 H0 : ℝ) : ℝ :=
  G0 * lkcs1 z0 z1 z2 + G1 * apuE z0 z1 + H0 * apuE1 z0 z1
/-- `h²` coefficient of the `𝔄`-link. -/
noncomputable def lkA2 (z0 z1 z2 z3 G0 G1 G2 H0 H1 : ℝ) : ℝ :=
  G0 * lkcs2 z0 z1 z2 z3 + G1 * lkcs1 z0 z1 z2 + G2 * apuE z0 z1 + H0 * lkds1 z0 z1 z2 + H1 * apuE1 z0 z1
/-- `h⁰` coefficient of the `𝔅`-link. -/
noncomputable def lkS0 (z0 z1 G0 : ℝ) : ℝ := G0 * apuA z0 z1
/-- `h¹` coefficient of the `𝔅`-link. -/
noncomputable def lkS1 (z0 z1 z2 G0 G1 H0 : ℝ) : ℝ :=
  G0 * lkss1 z0 z1 z2 + G1 * apuA z0 z1 + H0 * apuE z0 z1
/-- `h²` coefficient of the `𝔅`-link. -/
noncomputable def lkS2 (z0 z1 z2 z3 G0 G1 G2 H0 H1 : ℝ) : ℝ :=
  G0 * lkss2 z0 z1 z2 z3 + G1 * lkss1 z0 z1 z2 + G2 * apuA z0 z1 + H0 * lkus1 z0 z1 z2 + H1 * apuE z0 z1

/-! ### the link data -/

section Link

variable {α : Type*}

/-- The hypotheses on one link: all jets bounded, the remainders of the Taylor expansions of `ζ(q ± h)`, `G`, `H`. -/
structure LinkData (D : α → Prop) (hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η : α → ℝ) (Z0 S B : ℝ) : Prop where
  hD1 : ∀ a, D a → |hh a| ≤ 1
  hhdef : ∀ a, D a → hh a = t a ^ 3
  ht0 : ∀ a, D a → t a ≠ 0
  ht1 : ∀ a, D a → |t a| ≤ 1
  hZ0 : 0 ≤ Z0
  hS : 0 ≤ S
  hz0 : ∀ a, D a → |z0 a| ≤ Z0
  hz1 : ∀ a, D a → |z1 a| ≤ S
  hz2 : ∀ a, D a → |z2 a| ≤ B
  hz3 : ∀ a, D a → |z3 a| ≤ B
  he : SOB D hh 3 e
  hs : ∀ a, D a → |z1 a + (hh a * z2 a / 2 + hh a ^ 2 * z3 a / 6 + e a)| ≤ S
  hG0 : SOB D hh 0 G0
  hG1 : SOB D hh 0 G1
  hG2 : SOB D hh 0 G2
  hγ : SOB D hh 3 γ
  hH0 : SOB D hh 0 H0
  hH1 : SOB D hh 0 H1
  hη : SOB D hh 2 η

variable {D : α → Prop} {hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η : α → ℝ} {Z0 S B : ℝ}

/-- the increment `δ = h z₂/2 + h² z₃/6 + e`. -/
noncomputable def lkδ (hh z2 z3 e : α → ℝ) (a : α) : ℝ := hh a * z2 a / 2 + hh a ^ 2 * z3 a / 6 + e a
/-- `G = G₀ + h G₁ + h² G₂ + γ`. -/
noncomputable def lkG (hh G0 G1 G2 γ : α → ℝ) (a : α) : ℝ := G0 a + hh a * G1 a + hh a ^ 2 * G2 a + γ a
/-- `H = H₀ + h H₁ + η`. -/
noncomputable def lkH (hh H0 H1 η : α → ℝ) (a : α) : ℝ := H0 a + hh a * H1 a + η a

theorem LinkData.exδ (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (lkδ hh z2 z3 e) (fun _ => 0) (fun a => z2 a / 2) (fun a => z3 a / 6) := by
  refine ⟨L.he.congr fun a _ => by unfold lkδ; ring, SOB.const 0, ?_, ?_⟩
  · exact (SOB.bdd (M := B / 2) fun a ha => by
      rw [abs_div, abs_two]; linarith [L.hz2 a ha])
  · exact (SOB.bdd (M := B / 6) fun a ha => by
      rw [abs_div]; norm_num; linarith [L.hz3 a ha])

theorem LinkData.exG (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (lkG hh G0 G1 G2 γ) G0 G1 G2 :=
  ⟨L.hγ.congr fun a _ => by unfold lkG; ring, L.hG0, L.hG1, L.hG2⟩

theorem LinkData.exhH (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => hh a * lkH hh H0 H1 η a) (fun _ => 0) H0 H1 := by
  have h1 : SOB D hh 3 (fun a => hh a * η a) :=
    ((SOB.hh_pow (D := D) (hh := hh) 1).mul L.hη).congr fun a _ => by simp
  refine ⟨h1.congr fun a _ => by unfold lkH; ring, SOB.const 0, L.hH0, L.hH1⟩


theorem LinkData.hs' (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) (a : α) (ha : D a) :
    |z1 a + lkδ hh z2 z3 e a| ≤ S := by
  have := L.hs a ha
  unfold lkδ; exact this

theorem LinkData.remC (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    SOB D hh 3 (fun a => apuCs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) -
      (apuE (z0 a) (z1 a + lkδ hh z2 z3 e a) + hh a * apuO (z0 a) (z1 a + lkδ hh z2 z3 e a) +
        hh a ^ 2 * apuC2 (z0 a) (z1 a + lkδ hh z2 z3 e a))) ∧
    SOB D hh 3 (fun a => apuCs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) -
      (apuE1 (z0 a) (z1 a + lkδ hh z2 z3 e a) + hh a * apuO1 (z0 a) (z1 a + lkδ hh z2 z3 e a) +
        hh a ^ 2 * apuC21 (z0 a) (z1 a + lkδ hh z2 z3 e a))) := by
  obtain ⟨K, hK, hrem⟩ := apu2_C_remainder Z0 S L.hZ0 L.hS
  refine ⟨⟨K, hK, fun a ha => ?_⟩, ⟨K, hK, fun a ha => ?_⟩⟩
  · have := (hrem (z0 a) (t a) _ (L.hz0 a ha) (L.hs' a ha) (L.ht0 a ha) (L.ht1 a ha)).1
    rw [← L.hhdef a ha] at this; exact this
  · have := (hrem (z0 a) (t a) _ (L.hz0 a ha) (L.hs' a ha) (L.ht0 a ha) (L.ht1 a ha)).2
    rw [← L.hhdef a ha] at this; exact this

theorem LinkData.remS (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    SOB D hh 3 (fun a => apuSs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) -
      (apuA (z0 a) (z1 a + lkδ hh z2 z3 e a) + hh a * apuB (z0 a) (z1 a + lkδ hh z2 z3 e a) +
        hh a ^ 2 * apuS2 (z0 a) (z1 a + lkδ hh z2 z3 e a))) ∧
    SOB D hh 3 (fun a => apuSs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) -
      (apuE (z0 a) (z1 a + lkδ hh z2 z3 e a) + hh a * apuB1 (z0 a) (z1 a + lkδ hh z2 z3 e a) +
        hh a ^ 2 * apuS21 (z0 a) (z1 a + lkδ hh z2 z3 e a))) := by
  obtain ⟨K, hK, hrem⟩ := apu2_S_remainder Z0 S L.hZ0 L.hS
  refine ⟨⟨K, hK, fun a ha => ?_⟩, ⟨K, hK, fun a ha => ?_⟩⟩
  · have := (hrem (z0 a) (t a) _ (L.hz0 a ha) (L.hs' a ha) (L.ht0 a ha) (L.ht1 a ha)).1
    rw [← L.hhdef a ha] at this; exact this
  · have := (hrem (z0 a) (t a) _ (L.hz0 a ha) (L.hs' a ha) (L.ht0 a ha) (L.ht1 a ha)).2
    rw [← L.hhdef a ha] at this; exact this

/-- `E(ζ, s)` composed with `s = z₁ + δ` (third order). -/
theorem LinkData.exE (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => apuE (z0 a) (z1 a + lkδ hh z2 z3 e a)) (fun a => apuE (z0 a) (z1 a))
      (fun a => apuE1 (z0 a) (z1 a) * (z2 a / 2))
      (fun a => apuE1 (z0 a) (z1 a) * (z3 a / 6) + z0 a * apuE (z0 a) (z1 a) * (z2 a / 2) ^ 2 / 2) := by
  obtain ⟨M, hM0, hM⟩ := apu2_bnd Z0 S L.hZ0 L.hS
  have hZM : 0 ≤ Z0 * M := mul_nonneg L.hZ0 hM0
  refine Ex3.of_taylor3 L.hD1 (F := fun a => apuE (z0 a)) (F1 := fun a => apuE1 (z0 a))
    (F2 := fun a x => z0 a * apuE (z0 a) x) (F3 := fun a x => z0 a * apuE1 (z0 a) x)
    (M0 := M) (M1 := M) (M2 := Z0 * M) (M3 := Z0 * M) (S := S) (x0 := z1) hZM
    (fun a _ x => apu_hasDerivAt_E _ x) (fun a _ x => apu_hasDerivAt_E1 _ x)
    (fun a _ x => apu2_hasDerivAt_zE _ x) (fun a ha x hx => ?_) L.hz1 L.hs' L.exδ
  obtain ⟨b0, b1, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
  exact ⟨b0, b1, sj_b1 (L.hz0 a ha) b0 L.hZ0, sj_b1 (L.hz0 a ha) b1 L.hZ0⟩

theorem LinkData.exCs (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => apuCs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => apuE (z0 a) (z1 a)) (fun a => lkcs1 (z0 a) (z1 a) (z2 a))
      (fun a => lkcs2 (z0 a) (z1 a) (z2 a) (z3 a)) := by
  obtain ⟨M, hM0, hM⟩ := apu2_bnd Z0 S L.hZ0 L.hS
  have hSM : 0 ≤ (Z0 + S) * M := mul_nonneg (add_nonneg L.hZ0 L.hS) hM0
  have e2 := Ex3.of_taylor_h L.hD1 (F := fun a => apuO (z0 a)) (F1 := fun a => apuO1 (z0 a))
    (F2 := fun a x => z0 a * apuO (z0 a) x + x * apuE (z0 a) x) (M0 := M) (M1 := M) (M2 := (Z0 + S) * M)
    (S := S) (x0 := z1) hSM (fun a _ x => apu_hasDerivAt_O _ x) (fun a _ x => apu_hasDerivAt_O1 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, b2, b3, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      refine ⟨b2, b3, ?_⟩
      have := sj_b2 (L.hz0 a ha) hx b2 (hM (z0 a) x (L.hz0 a ha) hx).1 L.hZ0 L.hS
      linarith)
    L.hz1 L.hs' L.exδ
  have e3 := Ex3.of_taylor_h2 L.hD1 (F := fun a => apuC2 (z0 a)) (F1 := fun a => apuC21 (z0 a))
    (M0 := M) (M1 := M) (S := S) (x0 := z1) hM0 (fun a _ x => apu2_hasDerivAt_C2 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, -, -, -, -, -, b7, b8, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b7, b8⟩) L.hz1 L.hs' L.exδ
  have := ((L.exE.add e2).add e3).add (Ex3.of_sob L.remC.1)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by unfold lkcs1; ring)
    (fun a _ => by unfold lkcs2; ring)


theorem LinkData.exCs1 (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => apuCs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => apuE1 (z0 a) (z1 a)) (fun a => lkds1 (z0 a) (z1 a) (z2 a))
      (fun a => lkds2 (z0 a) (z1 a) (z2 a) (z3 a)) := by
  obtain ⟨M, hM0, hM⟩ := apu2_bnd Z0 S L.hZ0 L.hS
  have hZ : 0 ≤ Z0 := L.hZ0
  have hS : 0 ≤ S := L.hS
  have hZM : 0 ≤ Z0 * (Z0 * M) := mul_nonneg hZ (mul_nonneg hZ hM0)
  have hSM : 0 ≤ Z0 * M + (M + S * M) := by positivity
  have hSM1 : 0 ≤ Z0 * M + S * M := by positivity
  have e1 := Ex3.of_taylor3 L.hD1 (F := fun a => apuE1 (z0 a)) (F1 := fun a x => z0 a * apuE (z0 a) x)
    (F2 := fun a x => z0 a * apuE1 (z0 a) x) (F3 := fun a x => z0 a * (z0 a * apuE (z0 a) x))
    (M0 := M) (M1 := Z0 * M) (M2 := Z0 * M) (M3 := Z0 * (Z0 * M)) (S := S) (x0 := z1) hZM
    (fun a _ x => apu_hasDerivAt_E1 _ x) (fun a _ x => apu2_hasDerivAt_zE _ x)
    (fun a _ x => apu2_hasDerivAt_zE1 _ x)
    (fun a ha x hx => by
      obtain ⟨b0, b1, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b1, sj_b1 (L.hz0 a ha) b0 hZ, sj_b1 (L.hz0 a ha) b1 hZ,
        sj_b1 (L.hz0 a ha) (sj_b1 (L.hz0 a ha) b0 hZ |>.trans le_rfl) hZ⟩)
    L.hz1 L.hs' L.exδ
  have e2 := Ex3.of_taylor_h L.hD1 (F := fun a => apuO1 (z0 a))
    (F1 := fun a x => z0 a * apuO (z0 a) x + x * apuE (z0 a) x)
    (F2 := fun a x => z0 a * apuO1 (z0 a) x + (apuE (z0 a) x + x * apuE1 (z0 a) x))
    (M0 := M) (M1 := Z0 * M + S * M) (M2 := Z0 * M + (M + S * M)) (S := S) (x0 := z1) hSM
    (fun a _ x => apu_hasDerivAt_O1 _ x) (fun a _ x => apu2_hasDerivAt_OE _ x)
    (fun a ha x hx => by
      obtain ⟨b0, b1, b2, b3, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b3, sj_b2 (L.hz0 a ha) hx b2 b0 hZ hS, sj_b3 (L.hz0 a ha) hx b3 b0 b1 hZ hS⟩)
    L.hz1 L.hs' L.exδ
  have e3 := Ex3.of_taylor_h2 L.hD1 (F := fun a => apuC21 (z0 a))
    (F1 := fun a x => z0 a * apuC2 (z0 a) x + x * apuO (z0 a) x) (M0 := M) (M1 := Z0 * M + S * M) (S := S)
    (x0 := z1) hSM1 (fun a _ x => apu2_hasDerivAt_C21 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, b2, -, -, -, -, b7, b8, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b8, sj_b2 (L.hz0 a ha) hx b7 b2 hZ hS⟩) L.hz1 L.hs' L.exδ
  have := ((e1.add e2).add e3).add (Ex3.of_sob L.remC.2)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by unfold lkds1; ring)
    (fun a _ => by unfold lkds2; ring)

theorem LinkData.exSs (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => apuSs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => apuA (z0 a) (z1 a)) (fun a => lkss1 (z0 a) (z1 a) (z2 a))
      (fun a => lkss2 (z0 a) (z1 a) (z2 a) (z3 a)) := by
  obtain ⟨M, hM0, hM⟩ := apu2_bnd Z0 S L.hZ0 L.hS
  have hZ : 0 ≤ Z0 := L.hZ0
  have hS : 0 ≤ S := L.hS
  have hZM : 0 ≤ Z0 * M := mul_nonneg hZ hM0
  have hSM1 : 0 ≤ Z0 * M + S * M := by positivity
  have e1 := Ex3.of_taylor3 L.hD1 (F := fun a => apuA (z0 a)) (F1 := fun a => apuE (z0 a))
    (F2 := fun a => apuE1 (z0 a)) (F3 := fun a x => z0 a * apuE (z0 a) x)
    (M0 := M) (M1 := M) (M2 := M) (M3 := Z0 * M) (S := S) (x0 := z1) hZM
    (fun a _ x => apu_hasDerivAt_A _ x) (fun a _ x => apu_hasDerivAt_E _ x)
    (fun a _ x => apu_hasDerivAt_E1 _ x)
    (fun a ha x hx => by
      obtain ⟨b0, b1, -, -, b4, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b4, b0, b1, sj_b1 (L.hz0 a ha) b0 hZ⟩) L.hz1 L.hs' L.exδ
  have e2 := Ex3.of_taylor_h L.hD1 (F := fun a => apuB (z0 a)) (F1 := fun a => apuB1 (z0 a))
    (F2 := fun a x => z0 a * apuB (z0 a) x + x * apuA (z0 a) x) (M0 := M) (M1 := M)
    (M2 := Z0 * M + S * M) (S := S) (x0 := z1) hSM1 (fun a _ x => apu_hasDerivAt_B _ x)
    (fun a _ x => apu_hasDerivAt_B1 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, -, -, b4, b5, b6, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b5, b6, sj_b2 (L.hz0 a ha) hx b5 b4 hZ hS⟩) L.hz1 L.hs' L.exδ
  have e3 := Ex3.of_taylor_h2 L.hD1 (F := fun a => apuS2 (z0 a)) (F1 := fun a => apuS21 (z0 a))
    (M0 := M) (M1 := M) (S := S) (x0 := z1) hM0 (fun a _ x => apu2_hasDerivAt_S2 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, -, -, -, -, -, -, -, b9, b10⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b9, b10⟩) L.hz1 L.hs' L.exδ
  have := ((e1.add e2).add e3).add (Ex3.of_sob L.remS.1)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by unfold lkss1; ring)
    (fun a _ => by unfold lkss2; ring)

theorem LinkData.exSs1 (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => apuSs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => apuE (z0 a) (z1 a)) (fun a => lkus1 (z0 a) (z1 a) (z2 a))
      (fun a => lkus2 (z0 a) (z1 a) (z2 a) (z3 a)) := by
  obtain ⟨M, hM0, hM⟩ := apu2_bnd Z0 S L.hZ0 L.hS
  have hZ : 0 ≤ Z0 := L.hZ0
  have hS : 0 ≤ S := L.hS
  have hSM : 0 ≤ Z0 * M + (M + S * M) := by positivity
  have hSM1 : 0 ≤ Z0 * M + S * M := by positivity
  have e2 := Ex3.of_taylor_h L.hD1 (F := fun a => apuB1 (z0 a))
    (F1 := fun a x => z0 a * apuB (z0 a) x + x * apuA (z0 a) x)
    (F2 := fun a x => z0 a * apuB1 (z0 a) x + (apuA (z0 a) x + x * apuE (z0 a) x))
    (M0 := M) (M1 := Z0 * M + S * M) (M2 := Z0 * M + (M + S * M)) (S := S) (x0 := z1) hSM
    (fun a _ x => apu_hasDerivAt_B1 _ x) (fun a _ x => apu2_hasDerivAt_BA _ x)
    (fun a ha x hx => by
      obtain ⟨b0, -, -, -, b4, b5, b6, -⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b6, sj_b2 (L.hz0 a ha) hx b5 b4 hZ hS, sj_b3 (L.hz0 a ha) hx b6 b4 b0 hZ hS⟩)
    L.hz1 L.hs' L.exδ
  have e3 := Ex3.of_taylor_h2 L.hD1 (F := fun a => apuS21 (z0 a))
    (F1 := fun a x => z0 a * apuS2 (z0 a) x + x * apuB (z0 a) x) (M0 := M) (M1 := Z0 * M + S * M) (S := S)
    (x0 := z1) hSM1 (fun a _ x => apu2_hasDerivAt_S21 _ x)
    (fun a ha x hx => by
      obtain ⟨-, -, -, -, -, b5, -, -, -, b9, b10⟩ := hM (z0 a) x (L.hz0 a ha) hx
      exact ⟨b10, sj_b2 (L.hz0 a ha) hx b9 b5 hZ hS⟩) L.hz1 L.hs' L.exδ
  have := ((L.exE.add e2).add e3).add (Ex3.of_sob L.remS.2)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by unfold lkus1; ring)
    (fun a _ => by unfold lkus2; ring)

/-- **The `𝔄`-link.**  `G · Cs + h H · Cs'` has the expansion `lkA0 + h lkA1 + h² lkA2 + O(|h|³)`. -/
theorem LinkData.exA (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => lkG hh G0 G1 G2 γ a * apuCs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) +
        hh a * lkH hh H0 H1 η a * apuCs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => lkA0 (z0 a) (z1 a) (G0 a))
      (fun a => lkA1 (z0 a) (z1 a) (z2 a) (G0 a) (G1 a) (H0 a))
      (fun a => lkA2 (z0 a) (z1 a) (z2 a) (z3 a) (G0 a) (G1 a) (G2 a) (H0 a) (H1 a)) := by
  have := (Ex3.mul L.hD1 L.exG L.exCs).add (Ex3.mul L.hD1 L.exhH L.exCs1)
  refine this.congr (fun a _ => by ring) (fun a _ => by unfold lkA0; ring)
    (fun a _ => by unfold lkA1; ring) (fun a _ => by unfold lkA2; ring)

/-- **The `𝔅`-link.**  `G · Ss + h H · Ss'` has the expansion `lkS0 + h lkS1 + h² lkS2 + O(|h|³)`. -/
theorem LinkData.exS (L : LinkData D hh t z0 z1 z2 z3 e G0 G1 G2 γ H0 H1 η Z0 S B) :
    Ex3 D hh (fun a => lkG hh G0 G1 G2 γ a * apuSs (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a) +
        hh a * lkH hh H0 H1 η a * apuSs1 (z0 a) (t a) (z1 a + lkδ hh z2 z3 e a))
      (fun a => lkS0 (z0 a) (z1 a) (G0 a))
      (fun a => lkS1 (z0 a) (z1 a) (z2 a) (G0 a) (G1 a) (H0 a))
      (fun a => lkS2 (z0 a) (z1 a) (z2 a) (z3 a) (G0 a) (G1 a) (G2 a) (H0 a) (H1 a)) := by
  have := (Ex3.mul L.hD1 L.exG L.exSs).add (Ex3.mul L.hD1 L.exhH L.exSs1)
  refine this.congr (fun a _ => by ring) (fun a _ => by unfold lkS0; ring)
    (fun a _ => by unfold lkS1; ring) (fun a _ => by unfold lkS2; ring)

end Link

/-- info: 'FormalResearch.Special.LinkData.exA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.LinkData.exA

/-- info: 'FormalResearch.Special.LinkData.exS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.LinkData.exS

end FormalResearch.Special

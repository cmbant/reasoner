import FormalResearch.FourQubitEntropy.AH6Model

/-!
# Enclosure of the AH-6 computation stage by stage

If the parameters of `Par` are enclosed by the balls of a `Par Ball`, then every output of `stageA .. stageD`
(evaluated at `ℝ`) is enclosed by the corresponding output at `Ball` (`stageD_enc`).  The proofs are mechanical
applications of the enclosure lemmas of `AH6Ball` and `AH6Poly`, collected in the tactic `enc`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

theorem Enc.rat (p q : ℤ) : Enc (rat p q : ℝ) (rat p q : Ball) :=
  Enc.mul (Enc.ic p) (Enc.inv (Enc.ic q))

theorem enc_one : Enc (1 : ℝ) (ic 1 : Ball) := by
  have h := Enc.intCast 1
  rw [Int.cast_one] at h
  exact h

/-- Enclosure of a list literal. -/
theorem EncL.pair {a : ℝ} {A : Ball} {b : ℝ} {B : Ball} (ha : Enc a A) (hb : Enc b B) :
    EncL [a, b] [A, B] := EncL.cons ha (EncL.cons hb EncL.nil)

theorem EncL.single {a : ℝ} {A : Ball} (ha : Enc a A) : EncL [a] [A] := EncL.cons ha EncL.nil

/-- Closing tactic for enclosure goals. -/
macro "enc" : tactic =>
  `(tactic| repeat (first
    | assumption
    | apply Enc.add | apply Enc.mul | apply Enc.neg | apply Enc.inv | apply Enc.ic | apply enc_one | apply Enc.rat
    | apply addL_enc | apply mulL_enc | apply scaleL_enc | apply powL_enc | apply evalL_enc
    | apply derL_enc | apply EncL.single | apply EncL.pair | apply EncL.cons | apply EncL.nil
    | apply scalePow_enc | apply taylorL_enc | apply mob_enc))

structure ParEnc (p : Par ℝ) (P : Par Ball) : Prop where
  x : Enc p.x P.x
  l2 : Enc p.l2 P.l2
  l3 : Enc p.l3 P.l3
  lc : Enc p.lc P.lc
  la : Enc p.la P.la
  ld : Enc p.ld P.ld

structure StAEnc (s : StA ℝ) (S : StA Ball) : Prop where
  u : Enc s.u S.u
  c : Enc s.c S.c
  a : Enc s.a S.a
  d : Enc s.d S.d
  n1 : Enc s.n1 S.n1
  n2 : Enc s.n2 S.n2
  n3 : Enc s.n3 S.n3
  G1 : Enc s.G1 S.G1
  G2 : Enc s.G2 S.G2
  G3 : Enc s.G3 S.G3
  W1 : Enc s.W1 S.W1
  W2 : Enc s.W2 S.W2
  W3 : Enc s.W3 S.W3
  i21 : Enc s.i21 S.i21
  i31 : Enc s.i31 S.i31
  i32 : Enc s.i32 S.i32

theorem stageA_enc {p : Par ℝ} {P : Par Ball} (h : ParEnc p P) : StAEnc (stageA p) (stageA P) := by
  obtain ⟨hx, hl2, hl3, hlc, hla, hld⟩ := h
  constructor <;> simp only [stageA] <;> enc

structure StBEnc (t : StB ℝ) (T : StB Ball) : Prop where
  P : EncL t.P T.P
  q : EncL t.q T.q

theorem stageB_enc {s : StA ℝ} {S : StA Ball} (h : StAEnc s S) : StBEnc (stageB s) (stageB S) := by
  obtain ⟨hu, hc, ha, hd, hn1, hn2, hn3, hG1, hG2, hG3, hW1, hW2, hW3, hi21, hi31, hi32⟩ := h
  constructor <;> simp only [stageB] <;> enc

structure StC1Enc (c : StC1 ℝ) (C : StC1 Ball) : Prop where
  e0 : Enc c.e0 C.e0
  v0 : Enc c.v0 C.v0
  Pe0 : Enc c.Pe0 C.Pe0
  Pd0 : Enc c.Pd0 C.Pd0
  hh : Enc c.hh C.hh
  he : Enc c.he C.he
  hv : Enc c.hv C.hv
  a2 : Enc c.a2 C.a2
  a3 : Enc c.a3 C.a3
  b1 : Enc c.b1 C.b1
  g0 : Enc c.g0 C.g0
  g1 : Enc c.g1 C.g1
  q0 : Enc c.q0 C.q0
  q1 : Enc c.q1 C.q1
  eta2 : Enc c.eta2 C.eta2
  eta3 : Enc c.eta3 C.eta3

theorem stageC1_enc {p : Par ℝ} {P : Par Ball} {s : StA ℝ} {S : StA Ball} {t : StB ℝ} {T : StB Ball}
    (hp : ParEnc p P) (hs : StAEnc s S) (ht : StBEnc t T) :
    StC1Enc (stageC1 p s t) (stageC1 P S T) := by
  obtain ⟨hx, hl2, hl3, hlc, hla, hld⟩ := hp
  obtain ⟨hu, hc, ha, hd, hn1, hn2, hn3, hG1, hG2, hG3, hW1, hW2, hW3, hi21, hi31, hi32⟩ := hs
  obtain ⟨hP, hq⟩ := ht
  constructor <;> simp only [stageC1] <;> enc

structure StC2Enc (c : StC2 ℝ) (C : StC2 Ball) : Prop where
  b0 : Enc c.b0 C.b0
  a1 : Enc c.a1 C.a1
  a0 : Enc c.a0 C.a0
  k0 : Enc c.k0 C.k0
  k1 : Enc c.k1 C.k1
  gam : Enc c.gam C.gam

theorem stageC2_enc {c : StC1 ℝ} {C : StC1 Ball} (h : StC1Enc c C) :
    StC2Enc (stageC2 c) (stageC2 C) := by
  obtain ⟨he0, hv0, hPe0, hPd0, hhh, hhe, hhv, ha2, ha3, hb1, hg0, hg1, hq0, hq1, heta2, heta3⟩ := h
  constructor <;> simp only [stageC2] <;> enc

structure StD1Enc (d : StD1 ℝ) (D : StD1 Ball) : Prop where
  L : EncL d.L D.L
  AA : EncL d.AA D.AA
  BB : EncL d.BB D.BB
  CC : EncL d.CC D.CC
  EL : EncL d.EL D.EL

theorem stageD1_enc {t : StB ℝ} {T : StB Ball} {c : StC1 ℝ} {C : StC1 Ball} {d : StC2 ℝ} {D : StC2 Ball}
    (ht : StBEnc t T) (hc : StC1Enc c C) (hd : StC2Enc d D) :
    StD1Enc (stageD1 t c d) (stageD1 T C D) := by
  obtain ⟨hP, hq⟩ := ht
  obtain ⟨he0, hv0, hPe0, hPd0, hhh, hhe, hhv, ha2, ha3, hb1, hg0, hg1, hq0, hq1, heta2, heta3⟩ := hc
  obtain ⟨hb0, ha1, ha0, hk0, hk1, hgam⟩ := hd
  constructor <;> simp only [stageD1] <;> enc

theorem stageD2_enc {c : StC1 ℝ} {C : StC1 Ball} {d : StD1 ℝ} {D : StD1 Ball}
    (hc : StC1Enc c C) (hd : StD1Enc d D) : EncL (stageD2 c d) (stageD2 C D) := by
  obtain ⟨he0, hv0, hPe0, hPd0, hhh, hhe, hhv, ha2, ha3, hb1, hg0, hg1, hq0, hq1, heta2, heta3⟩ := hc
  obtain ⟨hL, hAA, hBB, hCC, hEL⟩ := hd
  simp only [stageD2]; enc

structure StD3Enc (d : StD3 ℝ) (D : StD3 Ball) : Prop where
  Pi : EncL d.Pi D.Pi
  cA : EncL d.cA D.cA
  cB : EncL d.cB D.cB
  cC : EncL d.cC D.cC
  tail : EncL d.tail D.tail

theorem stageD3_enc {c : StC1 ℝ} {C : StC1 Ball} {R : List ℝ} {RB : List Ball}
    (hc : StC1Enc c C) (hR : EncL R RB) : StD3Enc (stageD3 c R) (stageD3 C RB) := by
  obtain ⟨he0, hv0, hPe0, hPd0, hhh, hhe, hhv, ha2, ha3, hb1, hg0, hg1, hq0, hq1, heta2, heta3⟩ := hc
  have hPi : EncL (dl (dl R c.e0).1 c.e0).1 (dl (dl RB C.e0).1 C.e0).1 :=
    (dl_enc (dl_enc hR he0).1 he0).1
  have hr34 : Enc (rat 3 4 : ℝ) (rat 3 4 : Ball) := Enc.rat 3 4
  have hr54 : Enc (rat 5 4 : ℝ) (rat 5 4 : Ball) := Enc.rat 5 4
  have h0 : Enc (ic 0 : ℝ) (ic 0 : Ball) := Enc.ic 0
  have h1 : Enc (ic 1 : ℝ) (ic 1 : Ball) := Enc.ic 1
  exact ⟨hPi,
    mob_enc (scalePow_enc (Enc.add hr34 (Enc.neg h0)) (taylorL_enc hPi h0)),
    mob_enc (scalePow_enc (Enc.add h1 (Enc.neg hr34)) (taylorL_enc hPi hr34)),
    mob_enc (scalePow_enc (Enc.add hr54 (Enc.neg h1)) (taylorL_enc hPi h1)),
    taylorL_enc hPi hr54⟩

end FormalResearch.FourQubitEntropy.AH6

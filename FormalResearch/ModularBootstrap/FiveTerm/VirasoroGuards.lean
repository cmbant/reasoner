module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroDatum

/-!
# Axiom guards for the FIVE-0 Virasoro outer-function modules

`#print axioms` guards for the headline results of the modules `StripOuter*`, `SchwarzS*`, `BoundaryExt`,
`QFactor`, `QBounds`, `CombData`, `StripInverse`, `Virasoro*` (the guards of `VirasoroDatum` itself are in that file).
Kept in a separate leaf file so that adding a guard never forces a rebuild of the modules it guards.
-/

@[expose] public section

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.continuousOn_hbarA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.continuousOn_hbarA

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.hbarA_oneSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.hbarA_oneSub

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.hbarA_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.hbarA_conj

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_left

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_ge

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.StripOuter.re_hbarA_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.continuousWithinAt_sInt_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.continuousWithinAt_sInt_cut

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sInt_oncut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sInt_oncut

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sInt_sub_one_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sInt_sub_one_sq

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.exists_limit_qHat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.exists_limit_qHat

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.tendsto_qHat_slit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.tendsto_qHat_slit

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.qHat_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.qHat_sigma

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.qHat_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.qHat_conj

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.qHat_bounds_near_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.qHat_bounds_near_I

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.amp_aAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.amp_aAmp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.aAmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.aAmp_eq

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.Wslit_tanh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.Wslit_tanh

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sInv_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sInv_sigma

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sInv_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sInv_conj

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.sInv_mem_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.sInv_mem_strip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.differentiableAt_sInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.differentiableAt_sInv

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.continuousOn_sInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.continuousOn_sInv

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_diff

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_cont

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_conj

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_ne_zero

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_zero

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_local

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gout_real_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gout_real_pos

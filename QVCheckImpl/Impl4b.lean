import QVCheckImpl.Impl4

namespace QVCheck

/-- add `q • x` into the accumulator of sector `code` (all arrays have size `n²`) -/
def accAdd (acc : Array (Array Int)) (code : Nat) (q : Int) (x : Array Int) : Array (Array Int) :=
  acc.modify code fun a => tab a.size (fun i => gt a i + q * gt x i)

/-- zero accumulators -/
def accZero : Array (Array Int) := (List.range 256).toArray.map fun code => Array.replicate (nn code * nn code) 0

/-- the pair data of the terms of a block -/
def blockPairs (b : BlockD) : Array (Array (Nat × Nat × Int)) :=
  let L01 := letters01Of b; let L23 := letters23Of b; let sp := blkSp b
  (List.range b.2.2.1.length).toArray.map fun ti => pairsOf L01 L23 sp (b.2.2.2.getD ti [])

/-- the tables of a block: `01` side for source spins `(0,1)` and `23` side for source spins `(2,3)`, by target pair -/
def blockTab01 (b : BlockD) (pj : Nat) : Array (Array Int) :=
  mkTable (b.1 - 3) ((blkSp b).getD 0 0) ((blkSp b).getD 1 0) pj (letters01Of b)
def blockTab23 (b : BlockD) (pj : Nat) : Array (Array Int) :=
  mkTable (b.1 - 3) ((blkSp b).getD 2 0) ((blkSp b).getD 3 0) pj (letters23Of b)

/-- one sector `code` for target pair `pjA` with the `01` tables `T01` -/
def blockStep1 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : Nat) (T01 : Array (Array Int)) (code : Nat) (acc : Array (Array Int)) : Array (Array Int) :=
  if nn code > 0 && pA code == pjA then
    (List.range b.2.2.1.length).foldl (fun acc ti =>
      accAdd acc code (b.2.2.1.getD ti 0) (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[]))) acc
  else acc

/-- all sectors for the target pair `pjA` -/
def blockStep2 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : Nat) (acc : Array (Array Int)) : Array (Array Int) :=
  let T01 := blockTab01 b pjA
  (List.range 256).foldl (fun acc code => blockStep1 b pairs tabs23 pjA T01 code acc) acc

/-- add the contribution of one block to the accumulators -/
def runBlock (b : BlockD) (acc : Array (Array Int)) : Array (Array Int) :=
  let pairs := blockPairs b
  let tabs23 : Array (Array (Array Int)) := (List.range 16).toArray.map (blockTab23 b)
  (List.range 16).foldl (fun acc pjA => blockStep2 b pairs tabs23 pjA acc) acc

/-- all blocks -/
def runAll (blocks : List BlockD) : Array (Array Int) := blocks.foldl (fun acc b => runBlock b acc) accZero

end QVCheck

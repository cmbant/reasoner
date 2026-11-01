import QVCheckImpl.Impl4

namespace QVCheck

/-- add `q • x` into the accumulator of sector `code` -/
def accAdd (acc : Array (Array Int)) (code : Nat) (q : Int) (x : Array Int) : Array (Array Int) :=
  acc.modify code fun a => if a.size == 0 then x.map (q * ·) else tab a.size (fun i => gt a i + q * gt x i)

/-- run one block: all sectors, all its terms -/
def runBlock (b : BlockD) (acc : Array (Array Int)) : Array (Array Int) := Id.run do
  let ts := termsOf b
  let prep := prepare ts
  let a := ts.getD 0 default
  let ai := a.a - 3
  let sp := a.sp
  -- tables for the 23 side, one per target pair
  let tabs23 : Array (Array Int) := (List.range 16).toArray.map fun pj =>
    mkTable ai (sp.getD 2 0) (sp.getD 3 0) pj prep.letters23
  let mut acc := acc
  for pjA in [0:16] do
    let T01 := mkTable ai (sp.getD 0 0) (sp.getD 1 0) pjA prep.letters01
    for code in [0:256] do
      if nn code > 0 && pA code == pjA then
        let T23 := tabs23.getD (pB code) #[]
        for ti in [0:ts.size] do
          let c := ctil code T01 T23 (prep.groups.getD ti #[])
          acc := accAdd acc code (ts.getD ti default).q c
  return acc

end QVCheck

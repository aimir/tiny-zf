import TinyZF.Schemas

/-! Protected schemas before Boolean rewrites, with the same guards and parameter permutation. -/
namespace TinyZF.Source

/-- The corrected published ICS source before the selected rewrites. -/
def originalProtected (k : Fin 5) (p1 p2 p3 : Nat) : Nat :=
  match k.val with
  | 0 => -- POW
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wex p3 (wal p2 (wim (wal p3 (wim (wel p3 p2) (wel p3 p1))) (wel p2 p3))))
  | 1 => -- UNI
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wex p3 (wal p2 (wim (wex p3 (wa (wel p2 p3) (wel p3 p1))) (wel p2 p3))))
  | 2 => -- ICS
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wex p3 (wa (wal p2 (wa (wim (wel p2 p1) (wim (wex p1 p3) (wel p2 p3))) (wim (wel p2 p3) (wex p1 p3)))) (wal p1 (wim (wel p1 p3) (wal p2 (wim p3 (wex p2 (wa (wel p2 p3) p3))))))))
  | 3 => -- B6a1
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wim (weq p1 p3) (wal p2 (weq p1 p3)))
  | _ => -- B6a2
    let p1 := safe p1 p2
    let p3 := safe p3 p2
    (wim (wel p1 p3) (wal p2 (wel p1 p3)))

end TinyZF.Source

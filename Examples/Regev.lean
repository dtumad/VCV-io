import VCVio

open Mathlib OracleSpec OracleComp AsymmEncAlg

def regevAsymmEnc (n m χ p : ℕ) (h: NeZero p) (herr: p > 2*χ) (hp2 : p > 1) : AsymmEncAlg unifSpec ProbComp
    (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ←$ᵗ Vector (Fin (2*χ + 1)) m
    let err := e.map (fun t ↦ (Fin.castLE herr t) - χ)
    return ((A, Vector.zipWith Fin.add (Vector.ofFn (Matrix.vecMul s.get A)) err), s)
  encrypt := λ msg (A, y) ↦ do
    let r2 ←$ᵗ Vector (Fin 2) m
    let r := (r2.map (Fin.castLE hp2)).get
    let yr := dotProduct r y.get
    let signal := if msg then p / 2 else 0
    return (Vector.ofFn (Matrix.mulVec A r), yr + signal)
  decrypt := λ (a, b) s ↦ do
    let sa := dotProduct s.get a.get
    let val := Fin.val (sa - b)
    return if val < p/4 then true else val < 3*p/4
  __ := ExecutionMethod.default

namespace Regev

variable (n m χ p : ℕ) (h: NeZero p) (herr: p > 2*χ) (hp2 : p > 1)

section sound

theorem isSound : (regevAsymmEnc n m χ p h herr hp2).IsSound := by
  rintro msg
  simp

  sorry

end sound

end Regev

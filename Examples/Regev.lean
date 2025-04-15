import VCVio

open Mathlib OracleSpec OracleComp AsymmEncAlg

-- Define vector addition more generally

-- #check AtLeastTwo

def regevAsymmEnc (n m χ p : ℕ) (herr: p > 2*χ) (hp2 : p > 1) : AsymmEncAlg ProbComp
    (M := Bool) (PK := Matrix (Fin n) (Fin m) (Fin p) × Vector (Fin p) m) (SK := Vector (Fin p) n) (C := Vector (Fin p) n × Fin p) where
  keygen := do
    have : NeZero p := ⟨by omega⟩
    let A ←$ᵗ Matrix (Fin n) (Fin m) (Fin p)
    let s ←$ᵗ Vector (Fin p) n
    let e ←$ᵗ Vector (Fin (2*χ + 1)) m
    let err := e.map (fun t ↦ (Fin.castLE herr t) - χ)
    return ((A, Vector.zipWith Fin.add (Vector.ofFn (Matrix.vecMul s.get A)) err), s)
  encrypt := λ (A, y) msg ↦ do
    have : NeZero p := ⟨by omega⟩
    let r2 ←$ᵗ Vector (Fin 2) m
    let r := (r2.map (Fin.castLE hp2)).get
    let yr := dotProduct r y.get
    let signal := if msg then p / 2 else 0
    return (Vector.ofFn (Matrix.mulVec A r), yr + signal)
  decrypt := λ s (a, b) ↦ do
    have : NeZero p := ⟨by omega⟩
    let sa := dotProduct s.get a.get
    let val := Fin.val (sa - b)
    return if val < p/4 then true else val < 3*p/4
  __ := ExecutionMethod.default

namespace Regev

variable (n m χ p : ℕ) (h: NeZero p) (herr: p > 2*χ) (hp2 : p > 1)

section sound

theorem isCorrect : (regevAsymmEnc n m χ p herr hp2).PerfectlyCorrect := by
  rintro msg
  simp [CorrectExp, regevAsymmEnc, AsymmEncAlg]
  rintro A s e r

  sorry

end sound

end Regev

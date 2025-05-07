import VCVio

open Lean OracleComp ENNReal

syntax (name := probThing)
  "Pr[" term " | " sepBy((sepBy(ident, ",") " ← " term),";") "]" : term

def BuildProdGen : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => Macro.throwUnsupported
  | src :: [] => `($src)
  | src :: sources => do
    let rcall ← BuildProdGen sources
    `(Prod.mk <$> $src <*> $rcall)

def BuildCond (cond : TSyntax `term)
    (vars : List (TSyntax `ident)) : MacroM (TSyntax `term) :=
  match vars with
  | [] => `($cond)
  | v :: [] => `(fun $v => $cond)
  | v :: vs => do
    let rcall ← BuildCond cond vs
    `(Function.uncurry fun $v => $rcall)


macro_rules
  | `(Pr[$cond | $vars1:ident,* ← $src1]) => do
    let vars_list : List (List (TSyntax `ident)) :=
      [(↑vars1 : Array (TSyntax `ident)).toList]
    let sources :=
      (↑vars1 : Array (TSyntax `ident)).toList.map (fun _ => src1)
    let call ← BuildProdGen sources
    let check ← BuildCond cond vars_list.flatten
    `(probEvent $call $check)

  | `(Pr[$cond | $vars1:ident,* ← $src1;
                 $vars2:ident,* ← $src2]) => do
    let vars_list : List (List (TSyntax `ident)) :=
      [(↑vars1 : Array (TSyntax `ident)).toList,
       (↑vars2 : Array (TSyntax `ident)).toList]
    let sources :=
      (↑vars1 : Array (TSyntax `ident)).toList.map (fun _ => src1) ++
      (↑vars2 : Array (TSyntax `ident)).toList.map (fun _ => src2)
    let call ← BuildProdGen sources
    let check ← BuildCond cond vars_list.flatten
    `(probEvent $call $check)

  | `(Pr[$cond | $vars1:ident,* ← $src1;
                 $vars2:ident,* ← $src2;
                 $vars3:ident,* ← $src3]) => do
    let vars_list : List (List (TSyntax `ident)) :=
      [(↑vars1 : Array (TSyntax `ident)).toList,
       (↑vars2 : Array (TSyntax `ident)).toList,
       (↑vars3 : Array (TSyntax `ident)).toList]
    let sources :=
      (↑vars1 : Array (TSyntax `ident)).toList.map (fun _ => src1) ++
      (↑vars2 : Array (TSyntax `ident)).toList.map (fun _ => src2) ++
      (↑vars3 : Array (TSyntax `ident)).toList.map (fun _ => src3)
    let call ← BuildProdGen sources
    let check ← BuildCond cond vars_list.flatten
    `(probEvent $call $check)

#check Lean.Parser.doElemParser

noncomputable example (F : Type _) [Field F] [SelectableType F] : Unit := by
  let t := Pr[∀ i : Fin 3, y[i] ≠ 0| y ←$ᵗ Vector F 3]
  let u := Pr[y[0] = x[0] ∧ x[1] ≠ y[2] | x, y ←$ᵗ Vector F 3]
  let v := Pr[(x ∧ y) ∨ (x ∧ !z) | x, y, z ←$ᵗ Bool]
  let w := Pr[b ∧ x[0] ≠ 0 | b ←$ᵗ Bool; x ←$ᵗ Vector F 3]
  let μ := Pr[b ∧ b' ∧ x * y = 1 | b, b' ←$ᵗ Bool; x, y ←$ᵗ F]
  let ν := Pr[xs[0] = x ∨ b = true | b ←$ᵗ Bool; x ←$ᵗ F; xs ←$ᵗ Vector F 5]
  exact ()

/-
Uma coisa que eu sei que é possível: Mudar completamente a sintaxe!

ContextFreeGrammar exercício1 of Nat variables and Char literals
with initial 42 where rules are
  1 --> a 2 b c d |
  2 --> λ
-/
import Lean
open Lean Elab Meta Term Parser

inductive Symbol where
  | terminal    : Char → Symbol
  | nonterminal : Char → Symbol

instance : Repr Symbol where
  reprPrec s _ := match s with
  | Symbol.terminal A => Std.Format.text A.toString
  | Symbol.nonterminal a => Std.Format.text a.toString

def Symbol.fromChar
  (c : Char) : Symbol
:=
  if Char.isLower c
  then Symbol.terminal c
  else Symbol.nonterminal c

def Symbol.fromString
  (s : String) : List Symbol
:= s.data.map Symbol.fromChar


structure ContextFreeRule where
  input : Char
  output : List (Symbol)

instance : Repr ContextFreeRule where
  reprPrec r _ := Std.Format.text r.input.toString ++ Std.Format.text " ↦ " ++ (r.output.map (Repr.reprPrec · 0)).foldr (Std.Format.append) ""

syntax (name := teste) ident " ↦ " ident : term

elab_rules : term
  | `(teste| $a:ident ↦ $b:ident) => do
    let aStr := a.getId.toString
    if aStr.length > 1 then throwError "Só pode ter uma coisa no lado esquerdo, brother"
    let bStr := b.getId.toString
    let aTerm ← `($(Lean.Syntax.mkCharLit aStr.data[0]!))
    let bTerm ← `(Symbol.fromString $(Lean.Syntax.mkStrLit bStr))
    elabTerm (← `(ContextFreeRule.mk $aTerm $bTerm)) none

#eval A ↦ aaaaAbbb
#eval A ↦ Aa

#eval (⟨'A', [Symbol.nonterminal 'A', Symbol.terminal 'a']⟩ : ContextFreeRule)

structure ContextFreeGrammar where
  init : Char
  rules : List ContextFreeRule
deriving Repr

import LfaLean.ContextFreeGrammar.Defs
import Std.Data.HashSet
set_option linter.unusedSectionVars false

open Std

#check HashSet

inductive ContextFreeGrammar.reachable : ContextFreeGrammar V S → V → Prop
/- A variável inicial é sempre útil -/
  | init C : reachable C C.init
/- Uma variável é util se ela é output de uma variável útil -/
  | fromUsefull C v (u : ContextFreeRule V S) (usefull_u : reachable C u.input) (h : (Symbol.nonterminal v) ∈ u.output) : reachable C v

def ContextFreeGrammar.unreachable
  (C : ContextFreeGrammar V S) (v : V) : Prop
:= ¬C.reachable v

variable {V S : Type}
variable [BEq V] [BEq S] [LawfulBEq V] [LawfulBEq S]

protected def Helper.myFirstCFG : ContextFreeGrammar Char Char where
  init := 'S'
  rules := [
    ⟨'S', [Symbol.nonterminal 'S', Symbol.terminal '+', Symbol.nonterminal 'S']⟩,
    ⟨'S', [Symbol.nonterminal 'N']⟩,
    ⟨'N', [Symbol.terminal '0']⟩,
    ⟨'N', [Symbol.terminal 's', Symbol.nonterminal 'N']⟩,
    ⟨'U', [Symbol.terminal '⌣']⟩,
    ⟨'N', [Symbol.nonterminal 'S']⟩
  ]

protected def ContextFreeGrammar.consume (C : ContextFreeGrammar V S) (rule : ContextFreeRule V S)
  : List (ContextFreeGrammar V S)
:=  rule.output.filterMap (fun
      | Symbol.nonterminal v => some ⟨v, C.rules.removeAll [rule]⟩
      | _ => none)

protected theorem List.removeAll_removes
  : ∀ l : List V, x ∈ l → (l.removeAll [x]).length < l.length
:= by
  intro l
  intro hyp
  apply List.length_filter_lt_length_iff_exists.mpr
  apply Exists.intro x
  apply And.intro
  · assumption
  · intro h
    have this : elem x [x] := List.elem_cons_self
    rw [← this] at h
    exact (Bool.not_eq_self (elem x [x])).mp h

protected def ContextFreeGrammar.varRelevantRules (C : ContextFreeGrammar V S) (v : V)
  : List (ContextFreeRule V S)
:= C.rules.filter (fun x => x.input == v)

protected theorem ContextFreeGrammar.relevantRules_are_relevant (C : ContextFreeGrammar V S)
  : ∀ rule ∈ (C.varRelevantRules v), rule ∈ C.rules
:= by
  intro rule hyp
  rw [varRelevantRules.eq_def] at hyp
  have this : rule ∈ C.rules ∧ rule.input == v := List.mem_filter.mp hyp
  exact this.left

protected def Helper.usefullVars
  (C : ContextFreeGrammar V S)
  (acc : List (ContextFreeGrammar V S))
  (fuel : Nat)
  : List (ContextFreeGrammar V S) :=
  match fuel with
  | 0 => [C]
  | fuel' + 1 =>
    let relevant := C.varRelevantRules C.init
    let derived := relevant.flatMap (fun rule => C.consume rule)
    let recResults :=
      derived.flatMap (fun grammar => Helper.usefullVars grammar (C :: acc) fuel')
    C :: recResults

def ContextFreeGrammar.usefullVars (C : ContextFreeGrammar V S)
   : List V
:= sorry

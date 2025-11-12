import LfaLean.ContextFreeGrammar.Defs
import Std.Data.HashSet

open Std

#check HashSet

inductive ContextFreeGrammar.usefull : ContextFreeGrammar V S → V → Prop
/- A variável inicial é sempre útil -/
  | init C : usefull C C.init
/- Uma variável é util se ela é output de uma variável útil -/
  | fromUsefull C v (u : ContextFreeRule V S) (usefull_u : usefull C u.input) (h : (Symbol.nonterminal v) ∈ u.output) : usefull C v

def ContextFreeGrammar.useless
  (C : ContextFreeGrammar V S) (v : V) : Prop
:= ¬C.usefull v

variable {V S : Type}

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

variable [BEq V] [BEq S] [LawfulBEq V] [LawfulBEq S]

protected def Helper.deriveAndRemove (C : ContextFreeGrammar V S)
 (rule : ContextFreeRule V S) : List (ContextFreeGrammar V S)
:=
  let derived := rule.output.filterMap (
  fun symbol => match symbol with
    | Symbol.nonterminal v => some v
    | _ => none
  )
  let remainingRules := C.rules.removeAll [rule]
  derived.map (fun v => ⟨v, remainingRules⟩)

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

-- protected def Helper.deriveAndRemove_removes 

protected def Helper.varRelevantRules (C : ContextFreeGrammar V S) (v : V)
  : List (ContextFreeRule V S)
:= C.rules.filter (fun x => x.input == v)

protected theorem Helper.relevantRules_are_relevant (C : ContextFreeGrammar V S)
  : ∀ rule ∈ (Helper.varRelevantRules C v), rule ∈ C.rules
:= by
  intro rule hyp
  rw [Helper.varRelevantRules.eq_def] at hyp
  have this : rule ∈ C.rules ∧ rule.input == v := List.mem_filter.mp hyp
  exact this.left

protected def Helper.usefullVars (C : ContextFreeGrammar V S) (acc : List (ContextFreeGrammar V S))
  : List (ContextFreeGrammar V S)
:=
  let newGrammars : List (ContextFreeGrammar V S) := List.flatten $ (Helper.varRelevantRules C C.init).map (
    fun rule => Helper.deriveAndRemove C rule
  )

  let newUsefull := List.flatten $ newGrammars.map (
    fun grammar => Helper.usefullVars grammar (C :: acc)
  )

  newUsefull
termination_by C.rules.length
decreasing_by
  sorry


def ContextFreeGrammar.usefullVars (C : ContextFreeGrammar V S)
   : List V
:= sorry

-- protected def Helper.removeDuplicates [BEq α] : List α → List α
--   | []      => []
--   | a :: as => a :: Helper.removeDuplicates (as.filter (· != a))
-- termination_by l => l.length
-- decreasing_by
--   simp
--   have := List.length_filter_le (· != a) as
--   have h : as.length < as.length + 1 := by simp
--   exact Nat.lt_of_le_of_lt this h

-- protected def Helper.stepUsefull (rules : List $ ContextFreeRule V S) : V → (List V × List (ContextFreeRule V S))
--   | v =>
--   let ⟨vrules, nonvrules⟩ := rules.partition (fun r => r.input == v)
--   let outputs := vrules.map (ContextFreeRule.output)
--   let terminals := (outputs.flatten.filterMap Helper.isNonterminal?)
--   let nonvterminals := terminals.filter (· != v)
--   ⟨Helper.removeDuplicates nonvterminals, nonvrules⟩

-- protected theorem Helper.stepUsefull_decreases (rs : List $ ContextFreeRule V S) (v : V)
--   : (Helper.stepUsefull rs v).snd.length ≤ rs.length
-- := by
--   rw [Helper.stepUsefull]
--   simp
--   apply List.length_filter_le

-- protected theorem Helper.List.not_nil {l : List α} (h : ¬l = [])
--   : ∃a : α, a ∈ l
-- := by
--   cases l with
--   | nil => contradiction
--   | cons a as => apply Exists.intro a; simp

-- protected theorem Helper.removeDups_nil [BEq α]
--   : Helper.removeDuplicates ([] : List α) = []
-- := by rw [Helper.removeDuplicates.eq_def]

-- protected theorem Helper.removeDups_cons [BEq α] {as : List α}
--   : x ∈ Helper.removeDuplicates (a :: as) → x = a ∨ x ∈ Helper.removeDuplicates as
-- := by
--   intro h
--   induction as with
--   | nil =>
--     apply Or.inl
--     rw [
--       Helper.removeDuplicates,
--       List.filter.eq_1,
--       Helper.removeDups_nil,
--       List.mem_singleton
--     ] at h
--     exact h
--   | cons head tail hi =>


-- protected theorem Helper.in_remove_dupp_if_in_l [BEq α] {l : List α}
--   : (a ∈ Helper.removeDuplicates l) → a ∈ l
-- := by
--   intro h
--   induction l with
--   | nil =>
--     rw [Helper.removeDups_nil] at h
--     assumption
--   | cons x xs hi =>
--     simp
--     sorry

-- protected theorem Helper.either_less_or_equal (rs : List $ ContextFreeRule V S) (v : V)
--   : ¬(Helper.stepUsefull rs v).fst.isEmpty → (Helper.stepUsefull rs v).snd.length < rs.length
-- := by
--   rw [Helper.stepUsefull]
--   simp
--   intro h
--   have h := Helper.List.not_nil h
--   sorry


-- protected def Helper.usefullVars (rules : List $ ContextFreeRule V S)
--   (v : V) (acc : List V) : List V
-- :=
--   let ⟨nextUsefull, nextRules⟩ := Helper.stepUsefull rules v
--   let nextUsefull := nextUsefull.removeAll acc
--   match nextUsefull with
--   | [] => v :: acc
--   | _  =>  (nextUsefull.map (Helper.usefullVars nextRules · (v :: acc))).flatten
-- termination_by rules
-- decreasing_by
--   sorry

-- -- partial def Helper.usefullVars (C : ContextFreeGrammar V S) (acc : List V) : List V → List V
-- --   | [] => acc
-- --   | v :: vs =>
-- --     let usefullFromV := (Helper.stepUsefull C v).filter (· != v)
-- --     let newUseffulFromV := usefullFromV.removeAll acc
-- --     Helper.usefullVars C (v :: acc) (
-- --       Helper.removeDuplicates (newUseffulFromV ++ vs)
-- --     )

-- -- #eval Helper.usefullVars Helper.myFirstCFG ['S'] []

-- protected def Helper.usefullVars (rules : List $ ContextFreeRule V S) :

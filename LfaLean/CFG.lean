/-
Em haskell:
data symbol V S = terminal V | nonterminal S
-/
inductive Symbol
  (V : Type) (S : Type)
where
  | terminal (v : V) : Symbol V S
  | nonterminal (s : S) : Symbol V S

def reprAux : Symbol Char Char → Std.Format
  | Symbol.terminal c =>  Std.Format.text c.toString
  | Symbol.nonterminal c => Std.Format.text c.toString

instance (priority := low)  (A B : Type) [Repr A] [Repr B] : Repr (Symbol A B) where
  reprPrec s _ := match s with
  | Symbol.terminal A =>  repr A
  | Symbol.nonterminal a => repr a

/-
Em haskell:
newtype ContextFreeRule =
  { input :: V
  , output :: [Symbol V S]
  }
-/
structure ContextFreeRule
  (V : Type) (S : Type)
where
  input : V
  output : List (Symbol V S)

instance (priority := low) (A B : Type) [Repr A] [Repr B] : Repr (ContextFreeRule A B) where
  reprPrec r _ := (Repr.reprPrec r.input 0) ++ Std.Format.text " ↦ " ++ (r.output.map repr).foldr (Std.Format.append) ""

instance (priority := high) : Repr (ContextFreeRule Char Char) where
  reprPrec r _ := (reprAux $ Symbol.nonterminal r.input) ++ Std.Format.text " ↦ " ++ (r.output.map reprAux).foldr (Std.Format.append) ""

structure ContextFreeGrammar
  (V : Type) (S : Type) : Type
where
  init : V
  rules : List (ContextFreeRule V S)
deriving Repr

instance : Repr $ ContextFreeGrammar Char Char where
  reprPrec A _ := repr A.init ++ Std.Format.text "," ++ repr A.rules

/-
Diferença importante: O lean não é lazy e não tem ⊥'s!

```h
infty :: Nat
infty = Succ infty
```

não compilaria em Lean!
-/

/-
Definindo uma ContextFreeGrammar
-/
def myFirstCFG : ContextFreeGrammar Char Char where
  init := 'S'
  rules := [
    ⟨'S', [Symbol.nonterminal 'S', Symbol.terminal '+', Symbol.nonterminal 'S']⟩,
    ⟨'S', [Symbol.nonterminal 'N']⟩,
    ⟨'N', [Symbol.terminal '0']⟩,
    ⟨'N', [Symbol.terminal 's', Symbol.nonterminal 'N']⟩
  ]

#check myFirstCFG

inductive Symbol
  (V : Type) (S : Type)
where
  | terminal : S → Symbol V S
  | nonterminal : V → Symbol V S
deriving Repr, BEq

structure ContextFreeRule
  (V : Type) (S : Type)
where
  input : V
  output : List (Symbol V S)
deriving Repr, BEq

structure ContextFreeGrammar
  (V : Type) (S : Type) : Type
where
  init : V
  rules : List (ContextFreeRule V S)
deriving Repr, BEq

-- Pra printar bonitinho
section Representation

  protected def Symbol.reprAux : Symbol Char Char → Std.Format
    | Symbol.terminal c =>  Std.Format.text c.toString
    | Symbol.nonterminal c => Std.Format.text c.toString

  protected def List.segregate' (pred : a → a → Bool) : List a → List (List a) → List (List a)
    | [], lss => lss
    | a :: as, [] => List.segregate' pred as [[a]]
    | a :: as, ls :: lss =>
      if ls.all (pred a)
      then List.segregate' pred as ((a :: ls) :: lss)
      else List.segregate' pred as ([a] :: ls :: lss)

  protected def List.segregate (pred : a → a → Bool)
    : List a → List (List a)
  := List.reverse ∘ (List.segregate' pred · [])

  protected def ContextFreeRule.reprAux' : List (ContextFreeRule Char Char) → Std.Format
    | [] => ""
    | r :: rs => Std.Format.text r.input.toString ++ Std.Format.text " ↦ " ++ (r.output.map (Symbol.reprAux)).foldr Std.Format.append "" ++ Std.Format.text " | "
      ++ (rs.map (fun r => (r.output.map Symbol.reprAux).foldr Std.Format.append "")).foldr (Std.Format.append) ""

  protected def ContextFreeRule.reprAux'' (rss : List (ContextFreeRule Char Char))
    : Std.Format
  :=
    helper $ (List.segregate (fun r₁ r₂ => r₁.input == r₂.input) rss).map ContextFreeRule.reprAux'
    where
      helper (rss : List Std.Format) : Std.Format :=
        match rss with
        | [] => ""
        | [rs] => rs
        | rs :: rss => rs ++ Std.Format.line ++ helper rss


  instance : Repr $ ContextFreeGrammar Char Char where
    reprPrec A _ :=
    Std.Format.text "init := " ++ Symbol.reprAux (Symbol.nonterminal A.init) ++
    Std.Format.line ++ Std.Format.text "rules := " ++
    Std.Format.indentD (ContextFreeRule.reprAux'' A.rules)

end Representation

section Example
protected def Example.myFirstCFG : ContextFreeGrammar Char Char where
  init := 'S'
  rules := [
    ⟨'S', [Symbol.nonterminal 'S', Symbol.terminal '+', Symbol.nonterminal 'S']⟩,
    ⟨'S', [Symbol.nonterminal 'N']⟩,
    ⟨'N', [Symbol.terminal '0']⟩,
    ⟨'N', [Symbol.terminal 's', Symbol.nonterminal 'N']⟩,
    ⟨'U', [Symbol.terminal '⌣']⟩
  ]

#eval Example.myFirstCFG

end Example

/- Se eu consigo ir de w₁ para w₂ a partir de uma regra A ↦ w -/
inductive ContextFreeRule.rewrites (r : ContextFreeRule V S) : List (Symbol V S) → List (Symbol V S) → Prop
  | head s : r.rewrites (Symbol.nonterminal r.input :: s) (r.output ++ s)
  | cons x (hrs : r.rewrites s₁ s₂) : r.rewrites (x :: s₁) (x :: s₂)

/- Se eu consigo ir de w₁ para w₂ usando qualquer regra da minha gramática -/
def ContextFreeGrammar.rewrites (c : ContextFreeGrammar V S) (w₁ w₂ : List (Symbol V S))
  : Prop
:= ∃ r ∈ c.rules, r.rewrites w₁ w₂

/- O fecho reflexivo e transitivo da C.rewrites. Significa que de w₁ eu consigo chegar em w₂ usando só regras de derivação em C -/
inductive ContextFreeGrammar.derives (C : ContextFreeGrammar V S) : List (Symbol V S) → List (Symbol V S) → Prop
  | refl : derives C w w
  | tail : derives C w₁ w₂ → C.rewrites w₂ w₃ → derives C w₁ w₃

/- Se eu consigo ir de S até w -/
def ContextFreeGrammar.produces
  (C : ContextFreeGrammar V S) (w : List (Symbol V S)) : Prop
:= C.derives [Symbol.nonterminal C.init] w

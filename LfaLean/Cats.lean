universe u v

structure Category (Obj : Type u) : Type (max u (v + 1)) where
  -- Ops
  hom : Obj → Obj → Type v
  id (A : Obj) : hom A A
  comp : hom B C → hom A B → hom A C
  -- Laws
  comp_assoc {A B C D : Obj} (f : hom A B) (g : hom B C) (h : hom C D)
    : comp h (comp g f) = comp (comp h g) f
  id_comp (f : hom X Y) : comp (id Y) f = f
  comp_id (f : hom X Y) : comp f (id X) = f

def CategoryOfTypesWithFunctions : Category (Type) where
  hom := (· → ·)
  id := λ A => id
  comp := Function.comp
  comp_assoc f g h := by
    funext x
    simp [Function.comp]
  id_comp f := by
    funext x
    rw [Function.comp, id]
  comp_id f := by
    funext x
    rw [Function.comp, id]

structure Monoid (M : Type) where
  op : M → M → M
  id : M
  op_assoc (a b c : M) : op a (op b c) = op (op a b) c
  id_op (a : M) : op id a = a
  op_id (a : M) : op a id = a

def Category.fromMonoid (M : Monoid α) : Category PUnit where
  hom _ _ := α
  id _ := M.id
  comp := M.op
  comp_assoc f g h := M.op_assoc h g f
  id_comp := M.id_op
  comp_id := M.op_id

def myFirstMonoid : Monoid Nat where
  op := Nat.add
  id := Nat.zero
  op_assoc a b c := by symm; exact Nat.add_assoc a b c
  op_id := Nat.add_zero
  id_op := Nat.zero_add

def isomorphism (C : Category Obj) (f : C.hom A B) : Prop
  := ∃g, C.comp g f = C.id A ∧ C.comp f g = C.id B

theorem id_is_iso
  (C : Category Obj) : isomorphism C (C.id A)
:= by
  show ∃g, C.comp g (C.id A) = C.id A ∧ C.comp (C.id A) g = C.id A
  apply Exists.intro (C.id A)
  rw [C.comp_id]
  apply And.intro <;> rfl

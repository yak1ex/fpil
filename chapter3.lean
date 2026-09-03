/- 3. Overloading and Type Classes -/

/- 3.1. Positive Numbers -/

inductive Pos: Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7
-- failed to synthesize instance of type class OfNat Pos 7

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one))))))

-- def fourteen : Pos := seven + seven
-- failed to synthesize instance of type class HAdd Pos Pos ?m.3

-- def fortyNine : Pos := seven * seven
-- failed to synthesize instance of type class HMul Pos Pos ?m.3

/- 3.1.1. Classes and Instances -/
class Plus(α : Type) where
  plus : α → α → α

instance /- name -/ : Plus Nat where
  plus := Nat.add

@[instance_reducible]
def Plus_Nat : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven

-- #eval plus 5.2 917.25861
-- failed to synthesize instance of type class Plus Float

/- 3.1.2. Overload Addition -/
instance : Add Pos where
  add := Pos.plus

def fourteen' : Pos := seven + seven

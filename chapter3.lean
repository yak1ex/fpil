import Lean -- for Lean.Json.escape

/- 3. Overloading and Type Classes -/

/- 3.1. Positive Numbers -/

inductive Pos: Type where
  | one : Pos
  | succ : Pos → Pos

-- def seven : Pos := 7
-- failed to synthesize instance of type class OfNat Pos 7

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

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

/- 3.1.3. Conversion to Strings -/

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
    | Pos.one => "Pos.one"
    | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

#eval s!"There are {seven}" -- "There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}" -- "There are 7"

#eval seven -- 7

/- 3.1.4. Overloaded Multiplication -/

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one, seven * seven, Pos.succ Pos.one * seven] -- [7, 49, 14]

/- 3.1.5. Literal Numbers -/

instance : One Pos where
  one := Pos.one

#eval (1 : Pos) -- 1

inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4) -- LT4.three

#eval (0 : LT4) -- LT4.zero

-- #eval (4 : LT4) -- failed to synthesize instance of type class OfNat LT4 4

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8

-- def zero : Pos := 0 -- failed to synthesize instance of type class OfNat Pos 0

/- 3.1.6. Exercises -/

/- 3.1.6.1. Another Representation -/

structure Pos' where
  succ ::
  pred : Nat

#eval Pos'.succ 5 -- { pred := 5 }

def Pos'.add : Pos' → Pos' → Pos'
  | n, k => Pos'.succ (n.pred + k.pred + 1)

instance : Add Pos' where
  add := Pos'.add

#eval Pos'.succ 5 + (Pos'.succ 3) -- { pred := 9 }

instance : OfNat Pos' (n + 1) where
  ofNat := Pos'.succ n

#eval (3: Pos') -- { pred := 2 }
#eval (6: Pos') + (4: Pos') -- { pred := 9 }

def Pos'.mul : Pos' → Pos' → Pos'
  | 1, n => n
  | { pred := n + 1 }, k => (Pos'.succ n).mul k + k

instance : Mul Pos' where
  mul := Pos'.mul

#eval (1: Pos') * (2: Pos') -- { pred := 1 }
#eval (2: Pos') * (1: Pos') -- { pred := 1 }
#eval (2: Pos') * (3: Pos') -- { pred := 5 }

instance : ToString Pos' where
  toString x := toString (x.pred + 1)

#eval (3: Pos') -- 3
#eval (6: Pos') + (4: Pos') -- 10
#eval (1: Pos') * (2: Pos') -- 2
#eval (2: Pos') * (1: Pos') -- 2
#eval (2: Pos') * (3: Pos') -- 6

/- 3.1.6.2. Even Numbers -/

inductive NNEven: Type where
  | zero : NNEven
  | ssucc : NNEven -> NNEven

def NNEven.add : NNEven → NNEven → NNEven
  | NNEven.zero, k => k
  | NNEven.ssucc n, k => NNEven.ssucc (n.add k)

instance : Add NNEven where
  add := NNEven.add

#eval NNEven.zero + NNEven.zero -- NNEven.zero
#eval NNEven.zero + NNEven.zero.ssucc -- NNEven.ssucc (NNEven.zero)

def NNEven.mul : NNEven → NNEven → NNEven
  | NNEven.zero, _ => NNEven.zero
  | NNEven.ssucc n, k => n.mul k + k + k

instance : Mul NNEven where
  mul := NNEven.mul

#eval NNEven.zero * NNEven.zero -- NNEven.zero
#eval NNEven.zero * NNEven.zero.ssucc -- NNEven.zero
#eval NNEven.zero.ssucc * NNEven.zero -- NNEven.zero
#eval NNEven.zero.ssucc * NNEven.zero.ssucc -- NNEven.ssucc (NNEven.ssucc (NNEven.zero))

def NNEven.ToString (val : NNEven) : String :=
  let rec reduce val := match val with
    | NNEven.zero => 0
    | NNEven.ssucc n => 1 + reduce n
  s!"2 * {reduce val}"

instance : ToString NNEven where
  toString := NNEven.ToString

#eval NNEven.zero + NNEven.zero -- 2 * 0
#eval NNEven.zero + NNEven.zero.ssucc -- 2 * 1
#eval NNEven.zero * NNEven.zero -- 2 * 0
#eval NNEven.zero * NNEven.zero.ssucc -- 2 * 0
#eval NNEven.zero.ssucc * NNEven.zero -- 2 * 0
#eval NNEven.zero.ssucc * NNEven.zero.ssucc -- 2 * 2

/- 3.1.6.3. HTTP Requests -/

inductive HTTPMethod: Type where
  | GET
  | HEAD

structure HTTPRes where
  version : String
  code : Nat
  reason : String

def HTTPRes.ToString (res: HTTPRes) :=
  s!"{res.version} {res.code} {res.reason}"

instance : ToString HTTPRes where
  toString := HTTPRes.ToString

#check HTTPRes.mk "HTTP/1.0" 200 "OK" --  version := "HTTP/1.0", code := 200, reason := "OK" } : HTTPRes
#eval HTTPRes.mk "HTTP/1.0" 200 "OK" -- HTTP/1.0 200 OK

class HTTPReq (_ : HTTPMethod) where
  request : String -> String -> IO HTTPRes

def http_get (url : String) (http_version : String) : IO HTTPRes := do
  let stdout ← IO.getStdout
  stdout.putStrLn s!"GET {url} {http_version}"
  pure (HTTPRes.mk "HTTP/1.0" 200 "OK")

instance : HTTPReq HTTPMethod.GET where
  request := http_get

def http_head (url : String) (http_version : String) : IO HTTPRes := do
  let stdout ← IO.getStdout
  stdout.putStrLn s!"HEAD {url} {http_version}"
  pure (HTTPRes.mk "HTTP/1.0" 200 "OK")

instance : HTTPReq HTTPMethod.HEAD where
  request := http_head

def http_test : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn $ toString $ ←HTTPReq.request HTTPMethod.GET "http://example.com" "HTTP/1.0"
  stdout.putStrLn $ toString $ ←HTTPReq.request HTTPMethod.HEAD "https://example.com" "HTTP/1.0"

#eval http_test
/-
GET http://example.com HTTP/1.0
HTTP/1.0 200 OK
HEAD https://example.com HTTP/1.0
HTTP/1.0 200 OK
-/

/-
instance : HTTPReq GET where
  request := http_get
instance : HTTPReq HEAD where
  request := http_head
#eval http_test

/-
HEAD http://example.com HTTP/1.0
HTTP/1.0 200 OK
HEAD https://example.com HTTP/1.0
HTTP/1.0 200 OK
-/
/-
This is because:
```
instance : HTTPReq GET where
  request := http_get
```
is treated as
```
instance {GET} : HTTPReq GET where
  request := http_get
```
more specifically
```
instance {GET : HTTPMethod} : HTTPReq GET where
  request := http_get
```
`GET` is not a value but just a variable name.
-/
-/


/- 3.2. Type Classes and Polymorphism -/

/- 3.2.1. Checking Polymorphism Functions' Types -/

#check (IO.println) -- IO.println : ?m.1 → IO Unit
#check @IO.println -- IO.println : {α : Type u_1} → [ToString α] → α → IO Unit

/- 3.2.2. Defining Polymorphic Functions with Instance Implicits -/

def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents

def List.sumOfContents' [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents

def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sumOfContents -- 10

def fourPos : List Pos := [1, 2, 3, 4]
-- #eval fourPos.sumOfContents -- failed to synthesize instance of type class OfNat Pos 0

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

/- 3.2.3. Methods and Implicit Arguments -/

#check OfNat.ofNat -- OfNat.ofNat.{u} {α : Type u} (x✝ : Nat) [self : OfNat α x✝] : α

/- 3.2.4. Exercises -/

/- 3.2.4.1. Even Number Literals -/

instance : OfNat NNEven 0 where
  ofNat := NNEven.zero
instance [OfNat NNEven n] : OfNat NNEven (n + 2) where
  ofNat := NNEven.ssucc (OfNat.ofNat n)

#eval (0 : NNEven) -- 2 * 0
#eval (100 : NNEven) -- 2 * 50
-- #eval (99 : NNEven) -- failed to synthesize instance of type class OfNat NNEven 99

/- 3.2.4.2. Recursive Instance Search Depth -/

#eval (254 : NNEven)
-- #eval (256 : NNEven) -- failed to synthesize instance of type class OfNat NNEven 256

/- 3.3. Controlling Instance Search -/

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

#eval addNatPos 0 1 -- 1
#eval addPosNat 1 0 -- 1

/- 3.3.1. Heterogeneous Overloading -/

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat) -- 8
#eval (3 : Nat) + (5 : Pos) -- 8

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- #eval toString (HPlus.hPlus (3: Pos) (5 : Nat)) -- typeclass instance problem is stuck HPlus Pos Nat ?m.6

#eval (HPlus.hPlus (3 : Pos) (5: Nat) : Pos) -- 8

/- 3.3.2. Output Parameters -/

class HPlus' (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus' Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus' Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus'.hPlus (3 : Pos) (5 : Nat) -- 8
#eval HPlus'.hPlus (3 : Nat) (5 : Pos) -- 8

/- 3.3.3. Default Instances -/

instance [Add α] : HPlus' α α α where
  hPlus := Add.add

#eval HPlus'.hPlus (3 : Nat) (5 : Nat) -- 8

#check HPlus'.hPlus (5 : Nat) (3 : Nat) -- HPlus'.hPlus 5 3 : Nat

#check HPlus'.hPlus (5 : Nat) -- HPlus'.hPlus 5 : ?m.2 → ?m.3

@[default_instance]
instance [Add α] : HPlus' α α α where
  hPlus := Add.add

#check HPlus'.hPlus (5 : Nat) -- HPlus'.hPlus 5 : Nat → Nat

/- 3.3.4. Exercises -/

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p k := { x := p.x * k, y := p.y * k }

#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0 -- { x := 5.000000, y := 7.400000 }

/- 3.4. Arrays and Indexing -/

/- 3.4.1. Arrays -/

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size -- 4
#eval northernTrees[2] -- "elm"
--#eval northernTrees[8] -- failed to prove index is valid

/- 3.4.2. Non-Empty Lists -/

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n

#eval idahoSpiders.get? 0 -- some "Banded Garden Spider"
#eval idahoSpiders.get? 4 -- some "Cat-faced Spider"
#eval idahoSpiders.get? 5 -- none

def NonEmptyList.get'? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?

#eval idahoSpiders.get'? 0 -- some "Banded Garden Spider"
#eval idahoSpiders.get'? 4 -- some "Cat-faced Spider"
#eval idahoSpiders.get'? 5 -- none

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders : ¬idahoSpiders.inBounds 6 := by decide

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

#eval idahoSpiders.get 0 (by decide) -- "Banded Garden Spider"
#eval idahoSpiders.get 4 (by decide) -- "Cat-faced Spider"
--#eval idahoSpiders.get 5 (by decide) -- Tactic `decide` proved that the proposition idahoSpiders.inBounds 5 is false

/- 3.4.3. Overloading Indexing -/

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval idahoSpiders.head -- "Banded Garden Spider"
--#eval idahoSpiders[9] -- failed to prove index is valid

instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

#eval fourNats[(1: Pos)] -- 2

instance : GetElem (NonEmptyList α) Pos α
    (fun list n => list.inBounds  n.toNat) where
  getElem (xs : NonEmptyList α) (i : Pos) ok := xs[i.toNat]

#eval idahoSpiders[(1: Pos)] -- "Long-legged Sac Spider"

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

#eval ({ x := 3, y := 4 } : PPoint Nat)[false] -- 3

/- 3.5. Standard Classes -/

/- 3.5.1. Arithmetic -/

/- 3.5.2. Bitwise Operators -/

/- 3.5.3. Equality and Ordering -/

-- #check (fun (x : Nat) => 1 + x) == (Nat.succ ·) -- failed to synthesize instance of type class BEq (Nat → Nat)
#check (fun (x : Nat) => 1 + x) = (Nat.succ ·) -- (fun x => 1 + x) = fun x => x.succ : Prop
example : (fun (x : Nat) => 1 + x) = (Nat.succ ·) := by grind

#check 2 < 4 -- 2 < 4 : Prop
#check if 2 < 4 then 1 else 2 -- if 2 < 4 then 1 else 2 : Nat
#eval if 2 < 4 then 1 else 2 -- 1

--#check if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no" -- failed to synthesize instance of type class Decidable ((fun x => 1 + x) = fun x => x.succ)

instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
  le x y := LE.le x.toNat y.toNat

#check (1 : Pos) < (3 : Pos) -- 1 < 3 : Prop
--#eval (1 : Pos) < (3 : Pos) -- #check (1 : Pos) < (3 : Pos) -- 1 < 3 : Prop

instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))

--instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
--  (inferInstance : Decidable (x.toNat < y.toNat)) -- Type mismatch inferInstance

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))

/-
inductive Ordering where
  | lt
  | eq
  | gt
-/

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp

/-
instance : LT Pos := ltOfOrd
instance : LE Pos := leOfOrd
-/

/- 3.5.4. Hashing -/

/-
class Hashable (α : Type) where
  hash : α → UInt64
-/

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

#eval hash idahoSpiders -- 17196757539616925402

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ => false

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.branch l x r =>
      mixHash 1 $
        mixHash (hashBinTree l) $
          mixHash (hash x) $ hashBinTree r

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

#eval hash $ BinTree.branch BinTree.leaf 5 $ BinTree.branch BinTree.leaf 3 BinTree.leaf -- 14056269198372673594

/- 3.5.5. Deriving Standard Classes -/

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList

/- Inhabited, BEq, Repr, Hashable, Ord -/

/- 3.5.6. Appending -/

/-
class HAppend (α : TYpe) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
-/

instance : Append (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

#eval idahoSpiders ++ idahoSpiders
/-
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider",
           "Banded Garden Spider",
           "Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider"] }
-/

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]
/-
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider", "Trapdoor Spider"] }
-/

/- 3.5.7. Functors -/

#eval Functor.map (· + 5) [1, 2, 3] -- [6, 7, 8]
#eval Functor.map toString (some (List.cons 5 List.nil)) -- some "[5]"
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]] -- [[3, 2, 1], [6, 5, 4]]

#eval (· + 5) <$> [1, 2, 3] -- [6, 7, 8]
#eval toString <$> (some (List.cons 5 List.nil)) -- some "[5]"
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]] -- [[3, 2, 1], [6, 5, 4]]

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

/-
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β
  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
-/

/-
1. id <$> x == x
2. map (fun y => f (g y)) x == map f (map g x)
-/

/- 3.5.8. Messages You May Meet -/

--deriving instance ToString for NonEmptyList -- No deriving handlers have been implemented for class `ToString`

/- 3.5.9. Exercises -/

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys := match xs,ys with
    | [], ys => { head := ys.head, tail := ys.tail }
    | x :: xs, ys => { head := x, tail := xs ++ ys.head :: ys.tail }

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend
    | [], ys => { head := ys.head, tail := ys.tail }
    | x :: xs, ys => { head := x, tail := xs ++ ys.head :: ys.tail }

#eval ([] : List String) ++ idahoSpiders
/-
{ head := "Banded Garden Spider", tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider"] }
-/
#eval ([] : List String) ++ idahoSpiders == idahoSpiders -- true

#eval [""] ++ idahoSpiders
/-
{ head := "",
  tail := ["Banded Garden Spider", "Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider"] }
-/

instance : Functor BinTree where
  map f tree :=
    let rec map_tree f tree := match tree with
      | BinTree.leaf => BinTree.leaf
      | BinTree.branch l x r => BinTree.branch (map_tree f l) (f x) (map_tree f r)
    map_tree f tree

instance : Functor BinTree where
  map f tree := match tree with
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch l x r => BinTree.branch (f <$> l) (f x) (f <$> r)

instance : Functor BinTree where
  map f
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch l x r => BinTree.branch (f <$> l) (f x) (f <$> r)

#eval toString <$> (BinTree.branch BinTree.leaf 5 $ BinTree.branch BinTree.leaf 3 BinTree.leaf)
-- BinTree.branch (BinTree.leaf) "5" (BinTree.branch (BinTree.leaf) "3" (BinTree.leaf))

/- 3.6. Coercions -/

/- 3.6.1. Strings and Paths -/

def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trimAscii.copy
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f) -- String coereced to System.FilePath

/- 3.6.2. Positive Numbers -/

--#eval [1, 2, 3, 4].drop (2 : Pos) -- Application type mismatch

/-
class Coe (α : Type) (β : Type) where
  coe : α → β
-/

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos) -- [3, 4]
#check [1, 2, 3, 4].drop (2 : Pos) -- List.drop (Pos.toNat 2) [1, 2, 3, 4] : List Nat

/- 3.6.3. Chaining Coercions -/

def oneInt : Int := Pos.one
#check (Pos.one : Int) -- ↑Pos.one.toNat : Int

inductive A where
  | a
inductive B where
  | b
instance : Coe A B where
  coe _ := B.b
instance : Coe B A where
  coe _ := A.a
instance : Coe Unit A where
  coe _ := A.a
def coercedToB : B := ()
deriving instance Repr for B
#eval coercedToB -- B.b

def List.last? : List α → Option α
  | [] => none
  | [x] => x -- omit some
  | _ :: x :: xs => last? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

--def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
--  392
-- failed to synthesize instance of type class
--  OfNat (Option (Option (Option Nat))) 392

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)

def perhapsPerhapsPerhapsNat' : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

/- 3.6.4. Non-Empty Lists and Dependent Coercions -/

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

/-
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β
-/

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
#check ([1,2,3] : NonEmptyList Nat) -- { head := 1, tail := [2, 3] } : NonEmptyList Nat

/- 3.6.5. Coercing to Types -/

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

#eval foldMap stringMonoid toString [1,2,3] -- "123"

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap' (M: Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

#eval foldMap' stringMonoid toString [1,2,3] -- "123"

/-
instance : CoeSort Bool Prop where
  coe b := b = true
-/

/- 3.6.6. Coercing to Functions -/

/-
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
-/

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

--#eval add5 3 -- Function expected at add5 but this term has type Adder

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3 -- 8

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : Serializer := { Contents := String, serialize := JSON.string }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title: String) (R: Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"
/-
JSON.object
  [("title", JSON.string "Functional Programming in Lean"),
   ("status", JSON.number 200.000000),
   ("record", JSON.string "Programming is fun!")]
-/

/- 3.6.6.1. Aside: JSON as a String -/

#eval (5 : Float).toString -- "5.000000"

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropEndWhile (· == '0')
    (noTrailingZeros.dropEndWhile (· == '.')).copy
  else numString

#eval dropDecimals (5 : Float).toString -- "5"
#eval dropDecimals (5.2 : Float).toString -- "5.2"

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval ",".separate ["1","2"] -- "1,2"
#eval ",".separate ["1"] -- "1"
#eval ",".separate [] -- ""

#eval ",".intercalate ["1","2"] -- "1,2"
#eval ",".intercalate ["1"] -- "1"
#eval ",".intercalate [] -- ""

#eval Lean.Json.escape "\"Hello!\""

partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements => "[" ++ ", ".separate (elements.map asString) ++ "]"

#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
-- "{\"title\": \"Functional Programming in Lean\", \"status\": 200, \"record\": \"Programming is fun!\"}"

/- 3.6.7. Messages You May Meet -/

/- 3.6.8. Design Considerations -/

def lastSpider : Option String :=
  List.getLast? idahoSpiders

--def lastSpider' :=
--  List.getLast? idahoSpiders -- Application type mismatch

/- 3.7. Additional Conveniences -/

/- 3.7.1. Constructor Syntax for Instances -/

structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
 { latinName := "BEtula pendula",
   commonNames := ["silver birch", "warty birch"] }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]

class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName

/- 3.7.2. Examples -/

example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]}

example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n

/- 3.8. Summary -/

/- 3.8.1. Type Classes and Overloading -/

/- 3.8.2. Type Classes for Common Syntax -/

/- 3.8.3. Functors -/

/- 3.8.4. Deriving Instances -/

/- 3.8.5. Coercions -/

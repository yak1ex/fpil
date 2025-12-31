/- 1.1 Evaluating Expressions -/

#eval 1 + 2 -- 3
#eval 1 + 2 * 5 -- 11
#eval String.append "Hello, " "Lean!" -- "Hello, Lean!"
#eval String.append "great " (String.append "oak " "tree") -- "great oak tree"

#eval String.append "it is " (if 1 > 2 then "yes" else "no") -- "it is no"

/- 1.1.2 Exercises -/

#eval 42 + 19 -- 61
#eval String.append "A" (String.append "B" "C") -- "ABC"
#eval String.append (String.append "A" "B") "C" -- "ABC"
#eval if 3 == 3 then 5 else 7 -- 5
#eval if 3 == 4 then "equal" else "not equal" -- "not equal"

/- 1.2 Types -/

#eval (1 + 2 : Nat) -- 3
#eval (1 - 2 : Nat) -- 0
#eval (1 - 2 : Int) -- -1
#check (1 - 2: Int) -- 1 - 2 : Int
-- #check String.append ["hello", " "] "world"

/- 1.3 Functions and Definitions -/

def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean) -- "Hello Lean"

/- 1.3.1 Defining Functions -/

def add1 (n: Nat) : Nat := n + 1
#eval add1 7 -- 8

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval maximum (5 + 8) (2 * 7) -- 14
#check add1 -- add1 (n : Nat) : Nat
#check (add1) -- add1 : Nat → Nat
#check (maximum) -- maximum : Nat → Nat → Nat

example : Nat -> Nat := add1
example : Nat -> Nat -> Nat := maximum

#check maximum 3 -- maximum 3 : Nat → Nat
#check spaceBetween "Hello" -- spaceBetween "Hello" : String → String

/- 1.3.1.1 Exercises -/
def joinStringsWith (delim : String) (first : String) (second : String) : String :=
  String.append first (String.append delim second)
#check joinStringsWith ": " -- joinStringsWith ": " : String → String → String
def volume (height: Nat) (width: Nat) (depth: Nat) : Nat :=
  height * width * depth

/- 1.3.2 Defining Types -/

def Str : Type := String
def aStr : Str := "This is a string."

/- 1.3.2.1 Messages You May Meet -/

def NaturalNumber : Type := Nat
-- def thirtyEight : NaturalNumber := 38
def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat
def thirtyNine : N := 39

/- 1.4 Structures -/

#check 1.2 -- 1.2 : Float
#check -454.2123215 -- -454.2123215 : Float
#check 0.0 -- 0.0 : Float

#check 0 -- 0 : Nat
#check (0: Float) -- 0 : Float

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin -- { x := 0.000000, y := 0.000000 }
#eval origin.x -- 0.000000
#eval origin.y -- 0.000000

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 } -- { x := -6.500000, y := 32.200000 }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 } -- 5.000000

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- #check { x := 0.0, y := 0.0 }
#check ({ x := 0.0, y := 0.0 } : Point) -- { x: = 0.0, y := 0.0 } : Point
#check { x := 0.0, y := 0.0 : Point } -- { x: = 0.0, y := 0.0 } : Point

/- 1.4.1 Updating Structures -/

def zeroX' (p : Point) : Point :=
  { x := 0, y := p.y }

def zeroX (p : Point) : Point :=
  { p with x := 0 }

example : ∀ p, zeroX' p = zeroX p := by
  intro
  rfl

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval fourAndThree -- { x := 4.300000, y := 3.400000 }
#eval zeroX fourAndThree -- { x := 0.000000, y := 3.400000 }
#eval fourAndThree -- { x := 4.300000, y := 3.400000 }

/- 1.4.2 Behind the Scenes -/

#check Point.mk 1.5 2.8 -- { x:= 1.5, y := 2.8 } : Point
#check (Point.mk) -- Point.mk : Float → Float → Point

structure Point' where
  point ::
  x : Float
  y : Float

#check (Point'.point) -- Float → Float → Point'

#check (Point.x) -- Point.x : Point → Float
#check (Point.y) -- Point.y : Point → Float

#eval "one string".append " and another" -- "one string and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor -- { x := 4.000000, y := 3.000000 }

/- 1.4.3 Exercises -/

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume' (rp : RectangularPrism) : Float :=
  rp.height * rp.width * rp.depth

structure Segment where
  pt1 : Point
  pt2 : Point

def length (s : Segment) := distance s.pt1 s.pt2

#check RectangularPrism -- RectangularPrism : Type
#check (RectangularPrism.mk) -- ctangularPrism.mk : Float → Float → Float → RectangularPrism
#check (RectangularPrism.width) -- RectangularPrism.width : RectangularPrism → Float
#check (RectangularPrism.height) -- RectangularPrism.height : RectangularPrism → Float
#check (RectangularPrism.depth) -- RectangularPrism.depth : RectangularPrism → Float

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Hamster -- Hamster : Type
#check (Hamster.mk) -- Hamster.mk : String → Bool → Hamster
#check (Hamster.name) -- Hamster.name : Hamster → String
#check (Hamster.fluffy) -- Hamster.fluffy : Hamster → Bool

#check Book -- Book : Type
#check (Book.makeBook) -- Book.makeBook : String → String → Float → Book
#check (Book.title) -- Book.title : Book → String
#check (Book.author) -- Book.author : Book → String
#check (Book.price) -- Book.price : Book → Float

/- 1.5 Datatypes and Patterns -/

inductive Bool' where
  | false : Bool'
  | true : Bool'

#check true -- Bool.true : Bool
#check false -- Bool.false : Bool

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'

/- 1.5.1 Pattern Matching -/

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

#eval isZero Nat.zero -- true
#eval isZero 0 -- true
#eval isZero 5 -- false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5 -- 4
#eval pred 0 -- 0

def depth (p : Point3D) : Float :=
  match p with
  | { x := h, y := w, z := d } => d

def depth' (p : Point3D) : Float :=
  match p with
  | { x := _, y := _, z := d } => d

/- 1.5.2 Recursive Functions -/

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

/-
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
-/

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

/-
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
-/

/- 1.6 Polymorphism -/

structure PPoint (α : Type) where
  x : α
  y : α

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX) -- replaceX : (α : Type) → PPoint α → α → PPoint α
#check (replaceX Nat) -- replaceX Nat : PPoint Nat → Nat → PPoint Nat
#check replaceX Nat -- replaceX Nat : PPoint Nat → Nat → PPoint Nat
#check replaceX Nat natOrigin -- replaceX Nat natOrigin : Nat → PPoint Nat
#check replaceX Nat natOrigin 5 -- replaceX Nat natOrigin 5 : PPoint Nat
#eval replaceX Nat natOrigin 5 -- { x := 5, y := 0 }

inductive Sign where
  | pos
  | neg

def posOrNegThree (s: Sign) :
  match s with | Sign.pos => Nat | Sign.neg => Int :=
    match s with
    | Sign.pos => (3 : Nat)
    | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos -- 3

/- 1.6.1 Linked Lists -/

def primesUnder10 : List Nat := [2, 3, 5, 7]

/-
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
-/

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length' α ys)

def length'' (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length'' α ys)

/- 1.6.2 Implicit Arguments -/

def replaceX' {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX' natOrigin 5 -- { x := 5, y := 0 }

def length''' {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length''' ys)

#eval length''' primesUnder10 -- 4
#eval primesUnder10.length -- 4

#check List.length (α := Int) -- List.length : List Int → Nat

/- 1.6.3 More Built-In Datatypes -/

/- 1.6.3.1 Option -/

#eval primesUnder10.head? -- some 2
-- #eval [].head?
#eval [].head? (α := Int) -- none
#eval ([] : List Int).head? -- none

/- 1.6.3.2 Prod -/

def fives : String × Int := { fst := "five", snd := 5 }
def fives' : String × Int := ("five", 5)

def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens' : String × Int × Nat := ("VII", (7, 4 + 3))

example : sevens = sevens' := by rfl

/- 1.6.3.3 Sum -/

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals -- 3

/- 1.6.3.4 Unit -/

/- 1.6.3.5 Empty -/

/- 1.6.3.6 Naming: Sums, Products, and Units -/

/- 1.6.4 Messages You May Meet -/

/-
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
-/

/-
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
-/

/-
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (_ :: xs', _ :: ys') => sameLength xs' ys'
  | _ => false
-/

def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | _ :: xs' =>
    match ys with
    | _ :: ys' => sameLength xs' ys'
    | _ => false

/-
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
-/

inductive MyType (α : Type) : Type where
  | ctor : α → MyType α

/-
def ofFive : MyType := ctor 5
-/

inductive WoodSplittingTool where
  | axe
  | maul
  | froe

#eval WoodSplittingTool.axe -- WoodSplittingTool.axe

def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]

/-
#eval allTools
-/

inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr

def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]

#eval allFirewood

/- 1.6.5 Exercises -/
def lastElement {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _ :: ys => lastElement ys

#eval lastElement [1, 2, 3, 4, 5] -- some 5
#eval lastElement ["a", "b", "c"] -- some "c"
#eval lastElement ([] : List Nat) -- none

def List.findfirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys =>
    if predicate y then
      some y
    else
      findfirst? ys predicate

#eval List.findfirst? [1, 4, 6, 7, 8] (fun n => n % 2 == 0) -- some 4
#eval List.findfirst? ["apple", "banana", "cherry"] (fun s => s.length > 5) -- some "banana"
#eval List.findfirst? [3, 5, 7] (fun n => n > 10) -- none

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#eval Prod.switch ("hello", 42) -- (42, "hello")

inductive PetName' where
  | dog (name : String) : PetName'
  | cat (name : String) : PetName'

def animals' : List PetName' :=
  [PetName'.dog "Spot", PetName'.cat "Tiger", PetName'.dog "Fifi", PetName'.dog "Rex", PetName'.cat "Floof"]

def howManyDogs' (pets : List PetName') : Nat :=
  match pets with
  | [] => 0
  | PetName'.dog _ :: morePets => howManyDogs' morePets + 1
  | PetName'.cat _ :: morePets => howManyDogs' morePets

#eval howManyDogs' animals' -- 3

def zip {α β: Type} (xs : List α) (ys : List β) : List (α × β) :=
  match (xs, ys) with
  | ([], _) => []
  | (x :: xs', _) =>
    match ys with
    | [] => []
    | y :: ys' => (x, y) :: zip xs' ys'

#eval zip [1, 2, 3] ["a", "b", "c", "d"] -- [(1, "a"), (2, "b"), (3, "c")]
#eval zip [1, 2, 3, 4] ["x", "y"] -- [(1, "x"), (2, "y")]

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n with
  | Nat.zero => []
  | Nat.succ n' =>
    match xs with
    | y :: ys => y :: take n' ys
    | [] => []

#eval take 3 ["bolete", "oyster"] -- ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"] -- ["bolete"]
#eval take 0 ["bolete", "oyster"] -- []

def distrib {α β γ: Type} (p : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match p with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

#eval distrib ("name", (Sum.inl "Spot" : PetName)) -- Sum.inl ("name", "Spot")
#eval distrib ("name", (Sum.inr "Alice" : PetName)) -- Sum.inr ("name", "Alice")

def toSum {α : Type} (p : Bool × α) : α ⊕ α :=
  match p with
  | (true, a) => Sum.inl a
  | (false, a) => Sum.inr a

#eval toSum (true, 42) -- Sum.inl 42
#eval toSum (false, 99) -- Sum.inr 99

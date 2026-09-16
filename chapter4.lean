import chapter3

/- 4. Monads -/

/- 4.1. One API, Many Applications -/

/- 4.1.1. Checking for none: Don't Repeat Yourself -/

def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)

def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThird' (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

def firstThird'' (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))

/- 4.1.1.1. Infix Operators -/

infixl:55 " ~~> " => andThen

def firstThridInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

def firstThirdFifthSeventhInfix (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

/- 4.1.2. Propagating Error Messages -/

/-
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : a → Except ε α
deriving BEq, Hashable, Repr
-/

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x

def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
#eval get ediblePlants 2 -- Except.ok "sea buckthorn"
#eval get ediblePlants 4 -- Except.error "Index 4 not found (maximum is 3)"

def firstExcept (xs : List α) : Except String α :=
  get xs 0

def firstThirdExcept (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)

def firstThirdFifthExcept (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)

def firstThirdFifthSeventhExcept (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)

def andThenExcept (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

def firstThirdExcept' (xs : List α) : Except String (α × α) :=
  andThenExcept (get xs 0) fun first =>
  andThenExcept (get xs 2) fun third =>
  Except.ok (first, third)

def ok (x : α) : Except ε α := Except.ok x
def fail (err: ε) : Except ε α := Except.error err
def get' (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index{i} not found (maximum is {xs.length - 1})"
  | some x => ok x

infixl:55 " ~~> " => andThenExcept

def firstThirdExcept'' (xs : List α) : Except String  (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventhInfix' (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)

/- 4.1.3. Logging -/

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited,
     leftSum + hereSum + rightSum)

def sumAndFindEvens' : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def andThenLog (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
def okLog (x : β) : WithLog α β := {log := [], val := x}
def saveLog (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

def sumAndFindEvensLog : List Int → WithLog Int Int
  | [] => okLog 0
  | i :: is =>
    andThenLog (if isEven i then saveLog i else okLog ()) fun () =>
    andThenLog (sumAndFindEvensLog is) fun sum =>
    okLog (i + sum)

def inorderSumLog : BinTree Int → WithLog Int Int
  | BinTree.leaf => okLog 0
  | BinTree.branch l x r =>
    andThenLog (inorderSumLog l) fun leftSum =>
    andThenLog (saveLog x) fun () =>
    andThenLog (inorderSumLog r) fun rightSum =>
    okLog (leftSum + x + rightSum)

infixl:55 " ~~> " => andThenLog

def sumAndFindEvenLogs' : List Int → WithLog Int Int
  | [] => okLog 0
  | i :: is =>
    (if isEven i then saveLog i else okLog ()) ~~> fun () =>
    sumAndFindEvenLogs' is ~~> fun sum =>
    okLog (i + sum)

def inorderSumLog' : BinTree Int → WithLog Int Int
  | BinTree.leaf => okLog 0
  | BinTree.branch l x r =>
    inorderSumLog l ~~> fun leftSum =>
    saveLog x ~~> fun () =>
    inorderSumLog r ~~> fun rightSum =>
    okLog (leftSum + x + rightSum)

/- 4.1.4. Numbering Tree Nodes -/

open BinTree in
def aTree :=
  branch
    (branch
      (branch leaf "a" (branch leaf "b" leaf))
      "c"
      leaf)
    "d"
    (branch leaf "e" leaf)

def number (t: BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
    (helper 0 t).snd

#eval number aTree
/-
BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.branch (BinTree.leaf) (1, "b") (BinTree.leaf)))
    (2, "c")
    (BinTree.leaf))
  (3, "d")
  (BinTree.branch (BinTree.leaf) (4, "e") (BinTree.leaf))
-/

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def okState (x : α) : State σ α :=
  fun s => (s, x)
def getState : State σ σ :=
  fun s => (s, s)
def setState (s: σ) : State σ Unit :=
  fun _ => (s, ())
def andThenState (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'
infixl:55 " ~~> " => andThenState

def numberState (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => okState BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      getState ~~> fun n =>
      setState (n + 1) ~~>  fun () =>
      helper right ~~> fun numberedRight =>
      okState (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

/- 4.1.5. Monads: A Functional Design Pattern -/

/- 4.2. The Monad Type Class -/

/-
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
-/

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

def firstThirdFifthSeventhMonad [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
    "Peregrine falcon",
    "Saker falcon",
    "Golden eagle",
    "Gray-headed albatross",
    "Spur-winged goose",
    "Swift",
    "Anna's hummingbird"
]

#eval firstThirdFifthSeventhMonad (fun xs i => xs[i]?) slowMammals -- none
#eval firstThirdFifthSeventhMonad (fun xs i => xs[i]?) fastBirds -- some ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length -1 })"
  | some x => Except.ok x

#eval firstThirdFifthSeventhMonad getOrExcept slowMammals -- Except.error "Index 2 not found (maximum is 1)"
#eval firstThirdFifthSeventhMonad getOrExcept fastBirds -- Except.ok ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")

/- 4.2.1. General Monad Operations -/

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  getState >>= fun i =>
  setState (i + howMuch) >>= fun () =>
  pure i

#eval mapM increment [1, 2, 3, 4, 5] 0 -- (15, [0, 1, 3, 6, 10])

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    saveLog i
   else pure ()) >>= fun () =>
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5] -- { log := [2, 4], val := [1, 2, 3, 4, 5] }

/- 4.2.2. The Identitiy Monad -/

/-
def Id (t : Type) : Type := t
-/

instance : Monad Id where
  pure x := x
  bind x f := f x

def numbers := mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]

--def numbers' := mapM (do return · + 1) [1, 2, 3, 4, 5] -- typeclass instance problem is stuck

/- 4.2.3. The Monad Contract -/

/-
bind (pure v) f == f v
bind v pure == v
bind (bind v f) g == bind v (fun x => bind (f x) g)
-/

/- 4.2.4. Exercises -/

/- 4.2.4.1. Mapping on a Tree -/

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
    BinTree.mapM f l >>= fun left =>
    f x >>= fun cur =>
    BinTree.mapM f r >>= fun right =>
    pure $ BinTree.branch left cur right

open BinTree in
def bTree : BinTree Int :=
  branch
    (branch
      (branch leaf 0 (branch leaf 1 leaf))
      2
      leaf)
    3
    (branch leaf 4 leaf)

deriving instance Repr for BinTree

#eval BinTree.mapM increment bTree 0
#eval BinTree.mapM saveIfEven bTree

/- 4.2.4.2 The Option Monad Contract -/

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

/-
bind (pure v) f == f v
bind (pure x) f == bind (some x) f == f x

bind v pure == v
bind v pure
== bind v some
== match v with
   | none => none
   | some x => some x
== v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
== match (bind v f) with
   | none => none
   | some x => g x
== match (match v with
          | none => none
          | some x => f x) with
   | none => none
   | some x => g x
== match v with
   | none => none
   | some x => match (f x) with
               | none => none
               | some x => g x
bind v (fun x => bind (f x) g)
== match v with
   | none => none
   | some x => bind (f x) g
== match v with
   | none => none
   | some x => match (f x) with
               | none => none
               | some x => g x
-/

instance : Monad Option where
  pure x := some x
  bind opt next := none

/-
bind (pure v) f == f v
bind (pure v) f == bind (some v) f == none != f v -- BAD

bind v pure == v
bind v pure == none != v -- BAD

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g == none == bind v (fun x => bind (f x) g) -- OK
-/

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

/- 4.3. Example: Arithmetic in Monads -/

/- 4.3.1. Arithmetic Expressions -/

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))

/- 4.3.2. Evaluating Expressions -/

def evaluateOption' : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption' e1 >>= fun v1 =>
    evaluateOption' e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)

def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)
def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateOption fourteenDivided -- none

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrimExcept p v1 v2

def evaluateM [Monad m]
    (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2

#eval evaluateM applyPrim fourteenDivided -- none
#eval evaluateM applyPrimExcept fourteenDivided -- Except.error "Tried to divide 14 by zero"

/- 4.3.3. Further Effects -/

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim' [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM' [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM' applySpecial e1 >>= fun v1 =>
    evaluateM' applySpecial e2 >>= fun v2 =>
    applyPrim' applySpecial p v1 v2

/- 4.3.3.1. No Effects -/

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM' (m := Id) applyEmpty (prim plus (const 5) (const (-14))) -- -9

/- 4.3.3.2. Nondeterministic Search -/

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ => Many.none
  | Many.more x xs, f => (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
          pure (x :: answer))

def printList [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    printList xs

#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
/-
[7, 8]
[6, 9]
[5, 10]
[4, 5, 6]
[3, 5, 7]
[3, 4, 8]
[2, 6, 7]
[2, 5, 8]
[2, 4, 9]
[2, 3, 10]
[2, 3, 4, 6]
[1, 6, 8]
[1, 5, 9]
[1, 4, 10]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
[1, 2, 3, 4, 5]
-/

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

open Expr Prim NeedsSearch in
#eval
  (evaluateM' applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll -- [3, 6]
open Expr Prim NeedsSearch in
#eval
  (evaluateM' applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll -- []
open Expr Prim NeedsSearch in
#eval
  (evaluateM' applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll -- [9]

/- 4.3.3.3. Custom Environments -/

def Reader (ρ : Type) (α : Type) : Type := ρ → α
def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

/-
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
/-
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
-/
-/

def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM' applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- 9

/- 4.3.3.4. Exercises -/

/- 4.3.3.4.1. Checking Contracts -/

/-
def okState (x : α) : State σ α :=
  fun s => (s, x)
def getState : State σ σ :=
  fun s => (s, s)
def setState (s: σ) : State σ Unit :=
  fun _ => (s, ())
def andThenState (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'
infixl:55 " ~~> " => andThenState
/-
bind (pure v) f == f v
bind (pure v) f
== andThenState (okState v) f
== andThenState (fun s => (s, v)) f
== fun s => let (s', x) := (fun s => (s, v)) s
            f x s'
== fun s => f v s
== f v

bind v pure == v
bind v pure
== andThenState v okState
== fun s => let (s', x) := v s
            okState x s'
== fun s => let (s', x) := v s
            (s', x)
== fun s => v s
== v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
== andThenState (andThenState v f) g
== fun s => let (s'', x') := (andThenState v f) s
                           g x' s''
== fun s => let (s'', x') := (fun s => let (s', x) := v s)
                            f x s') s
                           g x' s''
== fun s => let (s'', x') := (let (s', x) := v s)
                            f x s')
                           g x' s''
== fun s => let (s', x) := v s
            let (s'', x') := f x s'
            g x' s''
bind v (fun x => bind (f x) g)
== andThenState v (fun x => andThenState (f x) g)
== fun s => let (s', x) := v s
            (fun x => andThenState (f x) g) x s'
== fun s => let (s', x) := v s
            (andThenState (f x) g) s'
== fun s => let (s', x) := v s
            (fun s => let (s'', x') := (f x) s
                      g x' s'') s'
== fun s => let (s', x) := v s
            (let (s'', x') := f x s'
                      g x' s'')
== fun s => let (s', x) := v s
            let (s'', x') := f x s'
            g x' s''
-/
-/

/-
instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

/-
bind (pure v) f == f v
bind (pure v) f
== match (Except.ok v) with
   | Except.error e => Except.error e
   | Except.ok x => f x
== f v

bind v pure == v
bind v pure
== match v with
   | Except.error e => Except.error e
   | Except.ok x => Except.ok x
== v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
== match (match v with
          | Except.error e => Except.error e
          | Except.ok x => f x) with
   | Except.error e => Except.error e
   | Except.ok x => g x
== match v with
   | Except.error e => Except.error e
   | Except.ok x => match (f x) with
                    | Except.error e => Except.error e
                    | Except.ok x => g x
bind v (fun x => bind (f x) g)
== match v with
   | Except.error e => Except.error e
   | Except.ok x => bind (f x) g
== match v with
   | Except.error e => Except.error e
   | Except.ok x => match (f x) with
                    | Except.error e => Except.error e
                    | Except.ok x => g x
-/
-/

/- 4.3.3.4.2. Readers with Failure -/

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x
def ReaderOption.bind
    (result : ReaderOption ρ α)
    (next : α → ReaderOption ρ β) : ReaderOption ρ β :=
  fun env =>
    match (result env) with
    | none => none
    | some x => next x env

example : ReaderOption.bind (ReaderOption.pure v) f = f v := by
  unfold ReaderOption.pure ReaderOption.bind
  funext
  simp

example  : ReaderOption.bind v ReaderOption.pure = v := by
  unfold ReaderOption.pure ReaderOption.bind
  funext env
  cases (v env) <;> simp

example :
  ReaderOption.bind (ReaderOption.bind v f) g = ReaderOption.bind v (fun x => ReaderOption.bind (f x) g) := by
  unfold ReaderOption.bind
  funext env
  cases (v env) <;> simp

/-
bind (pure v) f == f v
bind (pure v) f
== ReaderOption.bind (ReaderOption.pure v) f
== fun env =>
     match ((fun _ => some v) env) with
     | none => none
     | some x => f x env
== fun env => f v env
== f v

bind v pure == v
bind v pure
== ReaderOption.bind v ReaderOption.pure
== fun env =>
     match (v env) with
     | none => none
     | some x => (fun _ => some x) env
== fun env => v env
== v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
== ReaderOption.bind (ReaderOption.bind v f) g
== fun env =>
     match ((ReaderOption.bind v f) env) with
     | none => none
     | some x => g x env
== fun env =>
     match (match (v env) with
            | none => none
            | some x => f x env) with
     | none => none
     | some x => g x env
== fun env =>
     match (v env) with
     | none => none
     | some x => match (f x env) with
                 | none => none
                 | some x => g x env
bind v (fun x => bind (f x) g)
== fun env =>
     match (v env) with
     | none => none
     | some x => (bind (f x) g) env
== fun env =>
     match (v env) with
     | none => none
     | some x => match (f x env) with
                 | none => none
                 | some x =>  g x env
-/

instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def ReaderOption.read : ReaderOption ρ ρ := fun env => some env

def applyPrimReaderOption (op : String) (x : Int) (y : Int) : ReaderOption Env Int :=
  ReaderOption.read >>= fun env =>
  match env.lookup op with
  | none => fun _ => none
  | some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM' applyPrimReaderOption
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- some 9
open Expr Prim in
#eval
  evaluateM' applyPrimReaderOption
    (prim (other "unknown") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- none

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x
def ReaderExcept.bind
    (result : ReaderExcept ε ρ α)
    (next : α → ReaderExcept ε ρ β) : ReaderExcept ε ρ β :=
  fun env =>
    match (result env) with
    | Except.error e => Except.error e
    | Except.ok x => next x env

example : ReaderExcept.bind (ReaderExcept.pure v) f = f v := by
  unfold ReaderExcept.pure ReaderExcept.bind
  funext
  simp

example  : ReaderExcept.bind v ReaderExcept.pure = v := by
  unfold ReaderExcept.pure ReaderExcept.bind
  funext env
  cases (v env) <;> simp

example :
  ReaderExcept.bind (ReaderExcept.bind v f) g = ReaderExcept.bind v (fun x => ReaderExcept.bind (f x) g) := by
  unfold ReaderExcept.bind
  funext env
  cases (v env) <;> simp

/-
bind (pure v) f == f v
bind (pure v) f
== ReaderExcept.bind (ReaderExcept.pure v) f
== fun env =>
     match ((fun _ => Except.ok v) env) with
     | Except.error e => Except.error e
     | Except.ok x => f x env
== fun env => f v env
== f v

bind v pure == v
bind v pure
== ReaderExcept.bind v ReaderExcept.pure
== fun env =>
     match (v env) with
     | Except.error e => Except.error e
     | Except.ok x => (fun _ => Except.ok x) env
== fun env => v env
== v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
== ReaderExcept.bind (ReaderExcept.bind v f) g
== fun env =>
     match ((ReaderExcept.bind v f) env) with
     | Except.error e => Except.error e
     | Except.ok x => g x env
== fun env =>
     match (match (v env) with
            | Except.error e => Except.error e
            | Except.ok x => f x env) with
     | Except.error e => Except.error e
     | Except.ok x => g x env
== fun env =>
     match (v env) with
     | Except.error e => Except.error e
     | Except.ok x => match (f x env) with
                      | Except.error e => Except.error e
                      | Except.ok x => g x env
bind v (fun x => bind (f x) g)
== fun env =>
     match (v env) with
     | Except.error e => Except.error e
     | Except.ok x => (bind (f x) g) env
== fun env =>
     match (v env) with
     | Except.error e => Except.error e
     | Except.ok x => match (f x env) with
                      | Except.error e => Except.error e
                      | Except.ok x =>  g x env
-/

instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

def ReaderExcept.read : ReaderExcept ε ρ ρ := fun env => Except.ok env

def applyPrimReaderExcept (op : String) (x : Int) (y : Int) : ReaderExcept String Env Int :=
  ReaderExcept.read >>= fun env =>
  match env.lookup op with
  | none => fun _ => Except.error s!"function '{op}' is not found"
  | some f => pure (f x y)

open Expr Prim in
#eval
  evaluateM' applyPrimReaderExcept
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- Except.ok 9
open Expr Prim in
#eval
  evaluateM' applyPrimReaderExcept
    (prim (other "unknown") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- Except.error "function 'unknown' is not found"

/- 4.3.3.4.3. A Tracing Evaluator -/

inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α

instance : Monad (WithLog logged) where
  pure := okLog
  bind := andThenLog

def applyTraced
    (traceOp : ToTrace (Prim Empty))
    (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match traceOp with
  | ToTrace.trace op => saveLog (op, x, y)
  >>= fun () =>
  okLog (applyPrim' applyEmpty (m := Id) op x y)

deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim

open Expr Prim ToTrace in
#eval
  evaluateM' applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
-- { log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }

/- 4.4. do-Noation for Monads -/

def firstThirdFifthSeventhDo [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

def numberDo (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← getState
      setState (n + 1)
      let numberedRight ← helper right
      pure (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd

def mapMDo [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)

def mapMDo' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))

def incrementDo : State Nat Nat := do
  let n ← getState
  setState (n + 1)
  pure n

def numberDo' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure (BinTree.branch
        (← helper left)
        ((← incrementDo), x)
        (← helper right))
  (helper t 0).snd

/- 4.4.1. Exercises -/

def evaluateMDo [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do
    applyPrim'
      applySpecial
      p
      (← evaluateMDo applySpecial e1)
      (← evaluateMDo applySpecial e2)

def applyTracedDo
    (traceOp : ToTrace (Prim Empty))
    (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  match traceOp with
  | ToTrace.trace op => do
    saveLog (op, x, y)
    okLog (applyPrim' applyEmpty (m := Id) op x y)

open Expr Prim ToTrace in
#eval
  evaluateMDo applyTracedDo
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
--{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }

def applyPrimReaderDo (op : String) (x : Int) (y : Int) : Reader Env Int := do
  match (← read).lookup op with
  | none => pure 0
  | some f => pure (f x y)

open Expr Prim in
#eval
  evaluateMDo applyPrimReaderDo
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv -- 9

def firstThirdFifthSeventhDo' [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  pure (
    ← lookup xs 0,
    ← lookup xs 2,
    ← lookup xs 4,
    ← lookup xs 6
  )

/- 4.5. The IO Monad -/

#print Nat
/-
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/

#print String.toLower
/-
def String.toLower : String → String :=
fun s => String.map Char.toLower s
-/

#print List.head?
/-
def List.head?.{u} : {α : Type u} → List α → Option α :=
fun {α} x =>
  match x with
  | [] => none
  | a :: tail => some a
-/

#print IO
/-
@[reducible] def IO : Type → Type :=
EIO IO.Error
-/

#print IO.Error
/-
inductive IO.Error : Type
number of parameters: 0
constructors:
IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
IO.Error.otherError : UInt32 → String → IO.Error
IO.Error.resourceBusy : UInt32 → String → IO.Error
IO.Error.resourceVanished : UInt32 → String → IO.Error
IO.Error.unsupportedOperation : UInt32 → String → IO.Error
IO.Error.hardwareFault : UInt32 → String → IO.Error
IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
IO.Error.illegalOperation : UInt32 → String → IO.Error
IO.Error.protocolError : UInt32 → String → IO.Error
IO.Error.timeExpired : UInt32 → String → IO.Error
IO.Error.interrupted : String → UInt32 → String → IO.Error
IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
IO.Error.unexpectedEof : IO.Error
IO.Error.userError : String → IO.Error
-/

#print EIO
/-
def EIO : Type → Type → Type :=
fun ε α => EST ε IO.RealWorld α
-/

#print EST
/-
def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α
-/

#print EST.Out
/-
inductive EST.Out : Type → Type → Type → Type
number of parameters: 3
constructors:
EST.Out.ok : {ε σ α : Type} → α → Void σ → EST.Out ε σ α
EST.Out.error : {ε σ α : Type} → ε → Void σ → EST.Out ε σ α
-/

#print EST.pure
/-
protected def EST.pure : {α ε σ : Type} → α → EST ε σ α :=
fun {α ε σ} a s => EST.Out.ok a s
-/

#print EST.bind
/-
protected def EST.bind : {ε σ α β : Type} → EST ε σ α → (α → EST ε σ β) → EST ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EST.Out.ok a s => f a s
  | EST.Out.error e s => EST.Out.error e s
  -/

/- 4.6. Additional Conveniences -/

/- 4.6.1. Shared Argument Types -/

def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none

/- 4.6.2. Leading Dot Notation -/

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf
#check (.empty : BinTree Nat) -- BinTree.empty : BinTree Nat

/- 4.6.3. Or-Patterns -/

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

def condens : α ⊕ α → α
  | .inl x | .inr x => x

def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n

/-
def getTheAlpha : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => x  -- Unknown identifier `x`
-/

def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str

#check getTheString (.inl (20, "twenty")) -- getTheString (Sum.inl (20, "twenty")) : String
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String)) -- "twenty"
#eval getTheString (β := Nat) (.inl (20, "twenty")) -- "twenty"

#check getTheString (.inr (20, "twenty")) -- getTheString (Sum.inr (20, "twenty")) : String
#eval getTheString (.inr (20, "twenty")) -- "Some string"

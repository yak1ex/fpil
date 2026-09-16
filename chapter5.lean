import chapter3

/- 5. Functors, Applicative Functors, and Monads -/

/- 5.1. Structures and Inheritance -/

structure MythicalCreature where
  large : Bool
deriving Repr

#check MythicalCreature.mk -- MythicalCreature.mk (large : Bool) : MythicalCreature

#check MythicalCreature.large -- MythicalCreature.large (self : MythicalCreature) : Bool

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large := true
  vulnerability := "sunlight"

#check Monster.mk
-- Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster

#check Monster.toMythicalCreature -- Monster.toMythicalCreature (self : Monster) : MythicalCreature

#eval troll.toMythicalCreature -- { large := true }

def troll' : Monster := {large := true, vulnerability := "sunlight"}

--def troll'' : Monster := ⟨true, "sunlight"⟩
/-
Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  MythicalCreature
in the application
  Monster.mk true
-/

def troll'' : Monster := ⟨⟨true⟩, "sunlight"⟩

--#eval MythicalCreature.large troll
/-
Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.large troll
-/

/- 5.1.1. Multiple Inheritance -/

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"

#check MonstrousAssistant.mk -- MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant

#print MonstrousAssistant.toHelper
/-
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
-/

/- 5.1.1.1. Default Declarations -/

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large == (sc.size == Size.large)

def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by decide

/- 5.1.1.2. Type Class Inheritance -/

/- 5.2. Applicative Functors -/

/-
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
-/

/-
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
-/

-- E1 <*> E2 = Seq.seq E1 (fun () => E2)

#check some Add.add <*> some 4 -- some Add.add <*> some 4 : Option (Nat → Nat)
#check some Add.add <*> some 4 <*> some 7 -- some Add.add <*> some 4 <*> some 7 : Option Nat
#eval some Add.add <*> some 4 <*> some 7 -- some 11

structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

/-
1. id <$> x == x
id <$> Pair.mk x y
= Pair.mk x (id y)
= Pair.mk x y

2. map (fun y => f (g y)) x == map f (map g x)
f <$> g <$> Pari.mk x y
= f <$> Pari.mk x (g y)
= Pair.mk x (f (g y))
(fun z => f (g z)) <$> Pair.mk x y
= Pair.mk x (f (g y))
-/

/-
def Pair.pure (x : β) : Pair α β := _
/-
don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β
-/
-/

/-
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
/-
don't know how to synthesize placeholder for argument `first`
context:
β α : Type
x : β
⊢ α
-/
-/

/- 5.2.1. A Non-Monadic Applicative -/

/- 5.2.1.1. User Input -/

structure RawInput where
  name : String
  birthYear : String

/- 5.2.1.2. Subtypes -/

/- 5.2.1.2. Subtypes -/

/-
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
-/

def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by decide⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

/- 5.2.1.3. Validated Input -/

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α

instance : Functor (Validate ε) where
  map f
  | .ok x => .ok (f x)
  | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> x ()
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
      (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
        checkBirthYear year birthYearAsNat

deriving instance Repr for NonEmptyList
deriving instance Repr for CheckedInput

#eval checkInput 2023 {name := "David", birthYear := "1984"}
-- Validate.ok { name := "David", birthYear := 1984 }
#eval checkInput 2023 {name := "", birthYear := "2045"}
-- Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
-- Validate.errors { head := ("birth year", "Must be digits"), tail := [] }

/- 5.3. Applicative Contract -/

/-
1. pure id <*> v = v
2. pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
3. pure f <*> pure x = pure (f x)
4. u <*> pure x = pure (fun f => f x) <*> u
-/

/-
Applicative Option

some id <*> v = id <$> v = v

some (· ∘ ·) <*> some f <*> some g <*> some x
= some (f ∘ ·) <*> some g <*> some x
= some (f ∘ g) <*> some x
= some ((f ∘ g) x)
= some (f (g x))
some f <*> (some g <*> some x)
= some f <*> (some (g x))
= some (f (g x))

some f <*> some x
= f <$> some x
= some (f x)

some f <*> some x
= some (f x)
= some (fun g => g x) <*> some f
-/

/- 5.3.1. All Applicatives are Functors -/

def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x

class Applicative' (f: Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)

/- 5.3.2. All Monads are Applicative Functors -/

def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)

def seq' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β :=
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)

/-
seq (pure id) (fun () => v)
= pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y)
= pure id >>= fun g => v >>= fun y => pure (g y)
= v >>= fun y => pure (id y)
= v >>= fun y => pure y
= v >>= pure
= v
-/

/-
-/

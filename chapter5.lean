import chapter4

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
1. pure id <*> v = v
seq (pure id) (fun () => v)
= pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y)
= pure id >>= fun g => v >>= fun y => pure (g y)
= v >>= fun y => pure (id y)
= v >>= fun y => pure y
= v >>= pure
= v
-/

/-
2. pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
seq (seq (seq (pure (· ∘ ·)) (fun _ => u)) (fun _ => v)) (fun _ => w)
=((pure (· ∘ ·) >>= fun f =>
     u >>= fun x => pure (f x)) >>= fun g =>
   v >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
=((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
=((u >>= fun x =>
    pure (x ∘ ·)) >>= (fun g =>
    v >>= fun y =>
   pure (g y))) >>= fun h =>
  w >>= fun z =>
  pure (h z)
=(u >>= fun x =>
   pure (x ∘ ·) >>= fun g =>
  v >>= fun y => pure (g y)) >>= fun h =>
  w >>= fun z =>
  pure (h z)
=(u >>= fun x =>
   v >>= fun y =>
   pure (x ∘ y)) >>= fun h =>
  w >>= fun z =>
  pure (h z)
=u >>= fun x =>
 v >>= fun y =>
 pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
=u >>= fun x =>
 v >>= fun y =>
 w >>= fun z =>
 pure ((x ∘ y) z)
=u >>= fun x =>
 v >>= fun y =>
 w >>= fun z =>
 pure (x (y z))
=u >>= fun x =>
 v >>= fun y =>
 w >>= fun z =>
 pure (y z) >>= fun q
 pure (x q)
=u >>= fun x =>
 v >>= fun y =>
  (w >>= fun z =>
   pure (y z)) >>= fun q
 pure (x q)
=u >>= fun x =>
  (v >>= fun y =>
   w >>= fun z =>
   pure (y z)) >>= fun q
 pure (x q)
=u >>= fun x =>
 seq v (fun () => w) >>= fun q
 pure (x q)
=seq u (fun () => seq v (fun () => w))
-/

/-
3. pure f <*> pure x = pure (f x)
seq (pure f) (fun () => pure x)
=pure f >>= fun g =>
 pure x >>= fun y =>
 pure (g y)
=pure f >>= fun g =>
 pure (g x)
=pure (g x)
-/

/-
4. u <*> pure x = pure (fun f => f x) <*> u
seq u (fun () => pure x)
=u >>= fun f =>
 pure x >>= fun y =>
 pure (f y)
=u >>= fun f =>
 pure (f x)
=u >>= fun f =>
 pure ((fun g => g x) f)
=pure (fun g => g x) >>= fun h =>
 u >>= fun f =>
 pure (h f)
=seq (pure (fun f => f x)) (fun () => u)
-/

class Monad' (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)

/- 5.3.3. Additional Stipluations -/

def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }
def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }

#eval notFun <*> notArg
-- Validate.errors { head := "First error", tail := ["Second error"] }

def seq'' (f : Validate ε (α → β)) (x : Unit → Validate ε α) : Validate ε β :=
    Validate.andThen f fun g =>
    Validate.andThen (x ()) fun y =>
    pure (g y)

#eval seq'' notFun (fun () => notArg)
-- Validate.errors { head := "First error", tail := [] }

/- 5.4. Alternatives -/

/- 5.4.1. Recovery from Failure -/

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

def Validate.OrElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

class OrElse' (α : Type) where
  orElse : α → (Unit → α) → α

-- E1 <|> E2 = OrElse.orElse E1 (fun () => E2)

instance : OrElse (Validate ε α) where
  orElse := Validate.OrElse

def checkThat (condition : Bool)
    (field : Field) (msg : String) :
    Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

def checkCompany'' (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" <*>
    checkName input.name

class SeqRight' (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
  --seqRight (a : f α) (b: Unit → f β) : f β :=
  --  pure (fun _ x => x) <*> a <*> b ()

-- E1 *> E2 = SeqRight.seqRight E1 (fun () => E2)

def checkCompany' (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name

-- [Applicative f] pure f <*> E = f <$> E

def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970)
        ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y=>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970)
        ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
-- Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")

#eval checkLegacyInput ⟨"Johnny", "1963"⟩
-- Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")

#eval checkLegacyInput ⟨"", "1963"⟩
-- Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")

#eval checkLegacyInput ⟨"", "1970"⟩
/-
Validate.errors
  { head := ("birth year", "FIRM if a company"),
    tail := [("name", "Required"),
             ("birth year", "less than 1970"),
             ("birth year", "greater than 1970"),
             ("name", "Required")] }
-/

/- 5.4.2. The Alternative Class -/

class Alternative' (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α

instance [Alternative' f] : OrElse (f α) where
  orElse := Alternative'.orElse

instance : Alternative' Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

def guard' [Alternative' f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else Alternative'.failure

def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k

#eval (evenDivisors 20).takeAll -- [20, 10, 4, 2]

/- 5.4.3. Exercises -/

/- 5.4.3.1. Improve Validation Friendliness -/

inductive Validate_ (ε α : Type) : Type where
  | ok : α → Validate_ ε α
  | errors : ε → Validate_ ε α

def Validate_.andThen (val : Validate_ ε α)
    (next : α → Validate_ ε β) : Validate_ ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def Validate_.OrElse
    [Append ε]
    (a : Validate_ ε α)
    (b : Unit → Validate_ ε α) :
    Validate_ ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both

instance : Functor (Validate_ ε) where
  map f
  | .ok x => .ok (f x)
  | .errors errs => .errors errs

instance [Append ε] : Applicative (Validate_ ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> x ()
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

instance [Append ε] : OrElse (Validate_ ε α) where
  orElse := Validate_.OrElse

def Validate_.mapErrors (val : Validate_ ε α) (f : ε → ε') :
    Validate_ ε' α :=
  match val with
  | .ok x => .ok x
  | .errors err => .errors (f err)

def reportErrorField_ (f : Field) (msg : String) : Validate_ TreeError α :=
  .errors $ .field f msg

def checkName_ (name : String) :
    Validate_ TreeError {n : String // n ≠ ""} :=
  if h : name = "" then
    reportErrorField_ "name" "Required"
  else pure ⟨name, h⟩

def checkYearIsNat_ (year : String) : Validate_ TreeError Nat :=
  match year.trimAscii.toNat? with
  | none => reportErrorField_ "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear_ (thisYear year : Nat) :
    Validate_ TreeError {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportErrorField_ "birth year" s!"Must be no later than {thisYear}"
  else reportErrorField_ "birth year" "Must be after 1900"

def checkInput_ (year : Nat) (input : RawInput) :
    Validate_ TreeError (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName_ input.name <*>
      (checkYearIsNat_ input.birthYear).andThen fun birthYearAsNat =>
        checkBirthYear_ year birthYearAsNat

def checkThat_ (condition : Bool)
    (field : Field) (msg : String) :
    Validate_ TreeError Unit :=
  if condition then pure () else reportErrorField_ field msg

def checkCompany_ (input : RawInput) :
    Validate_ TreeError LegacyCheckedInput :=
  let val :=
    checkThat_ (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" *>
    .company <$> checkName_ input.name
  .mapErrors val (.path "Company")

/- Append ε requires Pure (Validate_ ε) -/
def checkSubtype_ [Append ε] {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate_ ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors err

def checkHumanBefore1970_ (input : RawInput) :
    Validate_ TreeError LegacyCheckedInput :=
  let val :=
    (checkYearIsNat_ input.birthYear).andThen fun y =>
      .humanBefore1970 <$>
        checkSubtype_ y (fun x => x > 999 ∧ x < 1970)
          (.field "birth year" "less than 1970") <*>
        pure input.name
  .mapErrors val (.path "HumanBefore1970")

def checkHumanAfter1970_ (input : RawInput) :
    Validate_ TreeError LegacyCheckedInput :=
  let val :=
    (checkYearIsNat_ input.birthYear).andThen fun y=>
      .humanAfter1970 <$>
        checkSubtype_ y (· > 1970)
          (.field "birth year" "greater than 1970") <*>
        checkName_ input.name
  .mapErrors val (.path "HumanAfter1970")

def checkLegacyInput_ (input : RawInput) :
    Validate_ TreeError LegacyCheckedInput :=
  checkCompany_ input <|>
  checkHumanBefore1970_ input <|>
  checkHumanAfter1970_ input

deriving instance Repr for Field
deriving instance Repr for TreeError

#eval checkLegacyInput_ ⟨"Johnny's Troll Groomers", "FIRM"⟩
-- Validate_.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")

#eval checkLegacyInput_ ⟨"Johnny", "1963"⟩
-- Validate_.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")

#eval checkLegacyInput_ ⟨"", "1963"⟩
-- Validate_.ok (LegacyCheckedInput.humanBefore1970 1963 "")

#eval checkLegacyInput_ ⟨"", "1970"⟩
/-
Validate_.errors
  (TreeError.both
    (TreeError.path
      "Company"
      (TreeError.both (TreeError.field "birth year" "FIRM if a company") (TreeError.field "name" "Required")))
    (TreeError.both
      (TreeError.path "HumanBefore1970" (TreeError.field "birth year" "less than 1970"))
      (TreeError.path
        "HumanAfter1970"
        (TreeError.both (TreeError.field "birth year" "greater than 1970") (TreeError.field "name" "Required")))))
-/

deriving instance ToString for Field

/- 任意の構造に対応してないのでちょっと手抜き -/
def report : TreeError → String
  | .both x xs => s!"{report x}\n{report xs}"
  | .field f r => s!"{f}: {r}"
  | .path c e => s!"[{c}]\n{report e}"

#eval match checkLegacyInput_ ⟨"", "1970"⟩ with
      | .errors e => report e
      | .ok _ => ""
/-
"[Company]\nbirth year: FIRM if a company\nname: Required\n[HumanBefore1970]\nbirth year: less than 1970\n[HumanAfter1970]\nbirth year: greater than 1970\nname: Required"
-/

def report' : TreeError → String :=
  let rec rep (cur : String) : TreeError → String
  | .both x xs => rep cur x ++ rep cur xs
  | .field f r => s!"[{cur}] {f}: {r}\n"
  | .path c e => rep c e
  rep "unknown"

#eval match checkLegacyInput_ ⟨"", "1970"⟩ with
      | .errors e => report' e
      | .ok _ => ""
/-
"[Company] birth year: FIRM if a company\n[Company] name: Required\n[HumanBefore1970] birth year: less than 1970\n[HumanAfter1970] birth year: greater than 1970\n[HumanAfter1970] name: Required\n"
-/

/- 5.5. Universes -/

#check Type -- Type : Type 1
#check Type 1 -- Type 1 : Type 2

#check Nat → Nat -- Nat → Nat : Type
#check Type → Type -- Type → Type : Type 1
#check Type 1 → Type 2 -- Type 1 → Type 2 : Type 3

#check (n : Nat) → n = n + 0 -- ∀ (n : Nat), n = n + 0 : Prop
#check Type → 2 + 2 = 4 -- ∀ (a : Type), 2 + 2 = 4 : Prop

/- 5.5.1. User Defined Types -/

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α

--def myListOfNat : MyList Type :=
--  .cons Nat .nil
/-
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  MyList Type
-/

/-
inductive MyList' (α : Type 1) : Type where
  | nil : MyList' α
  | cons : α → MyList' α → MyList' α
-/
/-
Invalid universe level in constructor `MyList'.cons`: Parameter has type
  α
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/

inductive MyList' (α : Type 1) : Type 1 where
  | nil : MyList' α
  | cons : α → MyList' α → MyList' α

def myListOfNat : MyList' Type :=
  .cons Nat .nil

/- 5.2.2. Universe Polymorphism -/

inductive MyList'' (α : Type u) : Type u where
  | nil : MyList'' α
  | cons : α → MyList'' α → MyList'' α

def myListOfNumbers : MyList'' Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat' : MyList'' Type :=
  .cons Nat .nil

def myListOfList : MyList'' (Type → Type) :=
  .cons MyList'' .nil

def myListOfNumbersExplicit : MyList''.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNatExplicit : MyList''.{1} Type :=
  .cons Nat .nil

def myListOfListExplicit : MyList''.{1} (Type → Type) :=
  .cons MyList'' .nil

inductive Sum' (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum' α β
  | inr : β → Sum' α β

def stringOrNat : Sum' String Nat := .inl "hello"
def typeOrType : Sum' Type Type := .inr Nat

--def stringOrType : Sum' String Type := .inr Nat
/-
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Sum' String Type
-/

inductive Sum'' (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum'' α β
  | inr : β → Sum'' α β

def stringOrType : Sum String Type := .inr Nat

/- 5.5.2.1. Writing Universe-Polymorphic Definitions -/

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

class MyApplicative (f: Type → Type) extends Functor f where
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

class MyMonad' (m : Type → Type) extends Applicative m where
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

class MyOrElse (α : Type) where
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

class MySeqRight (f : Type → Type) where
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

class MyAlternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α

instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse

instance : Alternative Option where
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

def guard' [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else Alternative.failure

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

/- 5.5.2.2. Prop and Polymorphism -/

def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world"
]

/- 5.6. Complete Definitions -/

/- 5.6.1. Functor -/

class MyFunctor (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
/- (α → β) : Type (u + 1) -/
/- (f α) (f β) : Type v -/

def simpleConst (x : α) (_ : β) : α := x
#eval [1, 2, 3].map (simpleConst "same") -- ["same", "same", "same"]

#check Function.const -- Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α

/- 5.6.2. Applicative -/

class MyPure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α

class MySeq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class MySeqRight' (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

class MySeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class MyApplicative' (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  -- fun a b => Seq.seq ((fun x _ => x) <$> a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
  -- fun a b => Seq.seq ((fun _ x => x) <$> a) b

/- 5.6.3. Monad -/

class MyBind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class MyMonad'' (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map f x      := bind x (Function.comp pure f)
  seq f x      := bind f fun y => Functor.map y (x ())
  seqLeft x y  := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

/- 5.6.4. Exercises -/

/-
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map f x      := bind x (Function.comp pure f)
  seq f x      := bind f fun y => Functor.map y (x ())
  seqLeft x y  := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
-/

/-
instance : Bind Option where
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
-/

/-
map f x := bind x (Function.comp pure f)
= match x with
  | none => none
  | some x => (Function.comp some f) x
= match x with
  | none => none
  | some x => some (f x)
-/

/-
seq f x := bind f fun y => Functor.map y (x ())
= match f with
  | none => none
  | some g => (fun y => Functor.map y (x ())) g
= match f with
  | none => none
  | some g => Functor.map g (x ())
= match f with
  | none => none
  | some g => match x () with
              | none => none
              | some y => some (g y)
-/

/-
seqLeft x y  := bind x fun a => bind (y ()) (fun _ => pure a)
= match x with
  | none => none
  | some z => (fun a => bind (y ()) (fun _ => some a)) z
= match x with
  | none => none
  | some z => bind (y ()) (fun _ => some z)
= match x with
  | none => none
  | some z => match (y ()) with
              | none => none
              | some zz => (fun _ => some z) zz
= match x with
  | none => none
  | some z => match (y ()) with
              | none => none
              | some _ => some z
-/

/-
seqRight x y := bind x fun _ => y ()
= match x with
  | none => none
  | some z => (fun _ => y ()) z
= match x with
  | none => none
  | some _ => y ()
-/

/-
instance : Bind (Except ε) where
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
-/

/-
map f x := bind x (Function.comp pure f)
= match x with
  | Except.error e => Except.error e
  | Except.ok x => (Function.comp Except.ok f) x
= match x with
  | Except.error e => Except.error e
  | Except.ok x => Except.ok (f x)
-/

/-
seq f x := bind f fun y => Functor.map y (x ())
= match f with
  | Except.error e => Except.error e
  | Except.ok y => (fun y => Functor.map y (x ())) y
= match f with
  | Except.error e => Except.error e
  | Except.ok y => Functor.map y (x ())
= match f with
  | Except.error e => Except.error e
  | Except.ok g => match x () with
                   | Except.error e => Except.error e
                   | Except.ok y => Except.ok (g y)
-/

/-
seqLeft x y := bind x fun a => bind (y ()) (fun _ => pure a)
= match x with
  | Except.error e => Except.error e
  | Except.ok a => (fun a => bind (y ()) (fun _ => Except.ok a)) a
= match x with
  | Except.error e => Except.error e
  | Except.ok a => bind (y ()) (fun _ => Except.ok a)
= match x with
  | Except.error e => Except.error e
  | Except.ok a => match y () with
                   | Except.error e => Except.error e
                   | Except.ok b => (fun _ => Except.ok a) b
= match x with
  | Except.error e => Except.error e
  | Except.ok a => match y () with
                   | Except.error e => Except.error e
                   | Except.ok _  => Except.ok a
-/

/-
seqRight x y := bind x fun _ => y ()
= match x with
  | Except.error e => Except.error e
  | Except.ok x => (fun _ => y ()) x
= match x with
  | Except.error e => Except.error e
  | Except.ok _ => y ()
-/

#print SeqRight

/-
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map f x      := bind x (Function.comp pure f)
  seq f x      := bind f fun y => Functor.map y (x ())
  seqLeft x y  := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

/-
Monad contract
bind (pure v) f = f v
bind v pure = v
bind (bind v f) g = bind v (fun x => bind (f x) g)
-/
-/

/-
Functor contract
1. (id <$> x =) map id x = x
map id x
= bind x (Function.comp pure id)
= bind x (id ∘ pure)
= bind x pure
= x
2. map (fun y => f (g y)) x = map f (map g x)
map (fun y => f (g y)) x
= bind x (Function.comp pure (fun y => f (g y))
= bind x (fun y => pure (f (g y)))
map f (map g x)
= map f (bind x (Function.comp pure g))
= map f (bind x (Function.comp pure g))
= bind (bind x (Function.comp pure g)) (Functionl.comp pure f)
= bind x (fun x => bind ((Function.comp pure g) x) (Functionl.comp pure f))
= bind x (fun x => bind (pure (g x)) (Functionl.comp pure f))
= bind x (fun x => (Functionl.comp pure f) (g x))
= bind x (fun y => pure (f (g y)))
-/

/-
Applicative contract
-- E1 <*> E2 = Seq.seq E1 (fun () => E2)

1. pure id <*> v = v
pure id <*> v
= seq (pure id) (fun () => v)
= bind (pure id) fun y => Functor.map y ((fun () => v) ())
= bind (pure id) fun y => Functor.map y v
= (fun y => Functor.map y v) id -- bind (pure v) f = f v
= Functor.map id v
= v -- Functor contract 1. (id <$> x =) map id x = x
2. pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
pure (· ∘ ·) <*> u <*> v <*> w
= seq (pure (· ∘ ·)) (fun () => u) <*> v <*> w
= bind (pure (· ∘ ·)) fun z => Functor.map z ((fun () => u) ()) <*> v <*> w
= bind (pure (· ∘ ·)) fun z => Functor.map z u) <*> v <*> w
= (fun z => Functor.map z u) (· o ·) <*> v <*> w
-- bind (pure v) f = f v
= Functor.map (· o ·) u <*> v <*> w
= bind u (Function.comp pure (· o ·)) <*> v <*> w
= seq (bind u (Function.comp pure (· o ·))) (fun () => v) <*> w
= bind (bind u (Function.comp pure (· o ·))) fun a => Functor.map a ((fun () => v) ()) <*> w
= bind (bind u (Function.comp pure (· o ·))) fun a => Functor.map a v <*> w
= bind u (fun z => bind ((Function.comp pure (· o ·)) z) (fun a => Functor.map a v)) <*> w
-- bind (bind v f) g = bind v (fun x => bind (f x) g)
= bind u (fun z => bind (pure (z o ·)) (fun a => Functor.map a v)) <*> w
= bind u (fun z => (fun a => Functor.map a v) (z o ·)) <*> w
-- bind (pure v) f = f v
= bind u (fun z => Functor.map (z o ·) v) <*> w
= seq (bind u (fun z => Functor.map (z o ·) v)) (fun () => w)
= bind (bind u (fun z => Functor.map (z o ·) v)) (fun a => Functor.map a ((fun () => w) ()))
= bind (bind u (fun z => Functor.map (z o ·) v)) (fun a => Functor.map a w)
= bind u (fun b => bind ((fun z => Functor.map (z o ·) v) b) (fun a => Functor.map a w))
-- bind (bind v f) g = bind v (fun x => bind (f x) g)
= bind u (fun b => bind (Functor.map (b o ·) v) (fun a => Functor.map a w))
= bind u (fun b => bind (bind v (Function.comp pure (b o ·))) (fun a => Functor.map a w))
= bind u (fun b => bind v (fun c => bind ((Function.comp pure (b o ·)) c) (fun a => Functor.map a w))
-- bind (bind v f) g = bind v (fun x => bind (f x) g)
= bind u (fun b => bind v (fun c => bind (pure ((b o ·) c)) (fun a => Functor.map a w))
= bind u (fun b => bind v (fun c => bind (pure (b o c)) (fun a => Functor.map a w))
-- bind (pure v) f = f v
= bind u (fun b => bind v (fun c => (fun a => Functor.map a w) (b o c)))
= bind u (fun b => bind v (fun c => Functor.map (b o c) w))
= bind u (fun b => bind v (fun c => bind w (Function.comp pure (b o c))))
= bind u (fun b => bind v (fun c => bind w (fun z => pure ((b o c) z))))
= bind u (fun b => bind v (fun c => bind w (fun z => pure (b (c z)))))

u <*> (v <*> w)
= u <*> seq v (fun () => w)
= u <*> bind v fun y => Functor.map y ((fun () => w) ())
= u <*> bind v fun y => Functor.map y w
= u <*> bind v fun y => bind w (Function.comp pure y)
= u <*> bind v fun y => bind w (fun x => pure (y x))
= seq u (fun () => bind v fun y => bind w (fun x => pure (y x)))
= bind u fun z => Functor.map z ((fun () => bind v fun y => bind w (fun x => pure (y x))) ())
= bind u fun z => Functor.map z (bind v fun y => bind w (fun x => pure (y x)))
= bind u fun z => bind (bind v fun y => bind w (fun x => pure (y x))) (Function.comp pure z)
= bind u fun z => bind v (fun a => bind ((fun y => bind w (fun x => pure (y x))) a) (Function.comp pure z))
-- bind (bind v f) g = bind v (fun x => bind (f x) g)
= bind u fun z => bind v (fun a => bind (bind w (fun x => pure (a x))) (Function.comp pure z))
= bind u fun z => bind v (fun a => bind w (fun b => bind ((fun x => pure (a x)) b) (Function.comp pure z))
= bind u fun z => bind v (fun a => bind w (fun b => bind (pure (a b)) (Function.comp pure z))
-- bind (bind v f) g = bind v (fun x => bind (f x) g)
= bind u fun z => bind v (fun a => bind w (fun b => bind (pure (a b)) (Function.comp pure z)))
= bind u fun z => bind v (fun a => bind w (fun b => (Function.comp pure z) (a b)))
= bind u fun z => bind v (fun a => bind w (fun b => pure (z (a b))))
-- bind (pure v) f = f v
3. pure f <*> pure x = pure (f x)
pure f <*> pure x
= seq (pure f) (fun () => pure x)
= bind (pure f) fun y => Functor.map y ((fun () => pure x) ())
= bind (pure f) fun y => Functor.map y (pure x)
= (fun y => Functor.map y (pure x)) f -- bind (pure v) f = f v
= Functor.map f (pure x)
= bind (pure x) (Function.comp pure f)
= (Function.comp pure f) x -- bind (pure v) f = f v
= pure (f x)
4. u <*> pure x = pure (fun f => f x) <*> u
u <*> pure x
= seq u (fun () => pure x)
= bind u fun y => Functor.map y ((fun () => pure x) ())
= bind u fun y => Functor.map y (pure x)
= bind u fun y => bind (pure x) (Fuction.comp pure y)
= bind u fun y => (Function.comp pure y) x -- bind (pure v) f = f v
= bind u fun y => pure (y x)
pure (fun f => f x) <*> u
= seq (pure (fun f => f x)) (fun () => u)
= bind (pure (fun f => f x)) fun y => Functor.map y ((fun () => u) ())
= bind (pure (fun f => f x)) fun y => Functor.map y u
= (fun y => Functor.map y u) (fun f => f x) -- bind (pure v) f = f v
= Functor.map (fun f => f x) u
= bind u (Function.comp pure (fun f => f x))
= bind u fun y => (Function.comp pure (fun f => f x)) y
= bind u fun y => pure ((fun f => f x) y)
= bind u fun y => pure (y x)
-/

/-
  map f x      := bind x (Function.comp pure f)
  seq f x      := bind f fun y => Functor.map y (x ())
-/

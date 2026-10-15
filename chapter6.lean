import chapter4

/- 6. Monad Transformers -/

/- 6.2. Monad Constrcution Kit -/

/-
1. monadLift (pure x : m α) = pure x
2. monadLift (x >>= f : m α) = (monadLift x : m α) >>= fun y => monadLift (f y)
-/

/- 6.2.1. Failure with OptionT -/

def MyOptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii
  if trimmed.isEmpty then
    failure
  else pure trimmed.copy

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none =>
    IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

/- 6.2.1.1. The Monad Instance -/

/-
instance [Monad m] : Monad (MyOptionT m) where
  pure x := pure (some x)
  bind action next := do
    match (← action) with
    | none => pure none
    | some v => next v
/-
Application type mismatch: The argument
  some x
has type
  Option α✝
but is expected to have type
  α✝
in the application
  pure (some x)
-/
-/

instance [Monad m] : Monad (MyOptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none
    | some v => next v : m (Option _))

structure MyOptionT' (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)

instance [Monad m] : Monad (MyOptionT' m) where
  pure x := ⟨pure (some x)⟩ -- same as MyOptionT'.mk (some x)
  bind action next := MyOptionT'.mk do
    match (← action.run) with
    | none => pure none
    | some v => (next v).run

def MyOptionT.mk (x : m (Option α)) : MyOptionT m α := x
def MyOptionT.run (x : MyOptionT m α) : m (Option α) := x -- not necessary for the following block

instance [Monad m] : Monad (MyOptionT m) where
  pure x := MyOptionT.mk (pure (some x))
  bind action next := MyOptionT.mk do
    match (← action) with
    | none => pure none
    | some v => next v

/-
bind (pure v) f = f v
bind (pure v) f
= OptionT.mk do
  match ← pure (some v) with
  | none => pure none
  | some x => f x
= OptionT.mk do
  let y ← pure (some v)
  match y with
  | none => pure none
  | some x => f x
= OptionT.mk
    (pure (some v)) >>= fun y =>
      match y with
      | none => pure none
      | some x => f x)
= OptionT.mk
    (match some v with
     | none => pure none
     | some x => f x)
= OptionT.mk (f v)
= f v

bind v pure = v
bind v pure
= OptionT.mk do
  match ← v with
  | none => pure none
  | some v => pure (some v)
= OptionT.mk (v >>= fun y => pure y)
= OptionT.mk v
= v

bind (bind v f) g == bind v (fun x => bind (f x) g)
bind (bind v f) g
= bind (OptionT.mk do
        match ← v with
        | none => pure none
        | some x => f x) g
= Option.mk do
    match ← (OptionT.mk do
           match ← v with
           | none => pure none
           | some x => f x) with
    | none => pure none
    | some x => g x
= Option.mk do
    match ← v with
    | none => pure none
    | some x => Option.mk do
                  match ← f x with
                  | none => pure none
                  | some x => g x
= Option.mk do
    match ← v with
    | none => pure none
    | some x => bind (f x) g
= Option.mk do
    match ← v with
    | none => pure none
    | some x => (fun x => bind (f x) g) x
= bind v (fun x => bind (f x ) g)
-/

/- 6.2.1.2. An Alternative Instance -/

instance [Monad m] : Alternative (MyOptionT m) where
  failure := MyOptionT.mk (pure none)
  orElse x y := MyOptionT.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()

/- 6.2.1.3. Lifting -/

instance [Monad m] : MonadLift m (MyOptionT m) where
  monadLift action := MyOptionT.mk do
    pure (some (← action))

/- 6.2.2. Exceptions -/

def MyExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

def MyExceptT.mk {ε α : Type u} (x : m (Except ε α)) : MyExceptT ε m α := x
def MyExceptT.run {ε α : Type u} (x : MyExceptT ε m α) : m (Except ε α) := x

instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (MyExceptT ε m) where
  pure x := MyExceptT.mk (pure (Except.ok x))
  bind result next := MyExceptT.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x

def MyExceptT.mk' (x : m (Except ε α)) : MyExceptT ε m α := x

/-
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := MyExceptT.mk' (pure (Except.ok x))
  bind result next := MyExceptT.mk' do
    match (← result) with
    | .error x => pure (.error e)
    | .ok x => next x

/-
tuck at solving universe constraint
  max ?u.26 ?u.27 =?= u
while trying to unify
  ExceptT ε m β✝ : Type v
with
  ExceptT.{max ?u.27 ?u.26, v} ε m β✝ : Type v
-/
-/

instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)

/- 6.2.2.1. Type Classes for Exceptions -/

class MyMonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α

inductive Err where
  | divByZero
  | notANumber : String → Err

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i

def divFrontend' [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""

/-
instance : MonadExcept Unit Option where
  throw _ := none
  tryCatch opt handler :=
    match opt with
    | none => handler ()
    | some x => some x
-/

/- 6.2.3. State -/

def MyStateT (σ : Type u)
    (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

instance [Monad m] : Monad (MyStateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err2 where
  | notALetter : Char → Err2
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters' (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
           pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList

def countLetters (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

def my_modify [MonadState σ m] (f : σ → σ) : m Unit :=
  modifyGet fun s => ((), f s)

class MyMonadState (σ : outParam (Type u)) (m: Type u → Type v) :
    Type (max (u+1) v) where
  get : m σ
  set : σ → m PUunit
  modifyGet : (σ → α × σ) → m α

/- 6.2.4. Of Classes and The Functions -/

def my_modify_the [MonadStateOf σ m] (f : σ → σ) : m Unit :=
  modifyGetThe σ fun s => ((), f s)

/- 6.2.5. Transformers and Id -/

/- 6.2.6. Exercises -/

/- 6.2.6.1. Monad Contract -/

/-
bind (pure v) f = f v
bind v pure = v
bind (bind v f) g == bind v (fun x => bind (f x) g)
-/

/-
1. monadLift (pure x : m α) = pure x
2. monadLift (x >>= f : m α) = (monadLift x : m α) >>= fun y => monadLift (f y)
-/

/-
instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do
    match (← action) with
    | none => pure none
    | some v => next v
-/
-- Monad contract already checked

/-
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))
-/

/-
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x
-/

/-
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)
-/

/-
def StateT (σ : Type u)
    (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'
-/

/-
instance [Monad m] : MonadLift m (StateT σ m) where
  monadLift action := StateT.mk fun st => do pure (← action, st)
-/

/- 6.2.6.2. Logging Transformer -/

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

class MyMonadState (σ : outParam (Type u)) (m: Type u → Type v) :
    Type (max (u+1) v) where
  get : m σ
  set : σ → m PUunit
  modifyGet : (σ → α × σ) → m α
-/

structure WithLog' (logged : Type u) (α : Type u) where
  log : List logged
  val : α
deriving Repr

def andThenLog' (result : WithLog' α β) (next : β → WithLog' α γ) : WithLog' α γ :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
def okLog' (x : β) : WithLog' α β := {log := [], val := x}
def saveLog' (data : α) : WithLog' α PUnit :=
  {log := [data], val := ()}

instance : Monad (WithLog' σ) where
  pure x := WithLog'.mk [] x
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

def WithLogT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (WithLog' σ α)

def WithLogT.mk (x : m (WithLog' σ α)) : WithLogT σ m α := x
def WithLogT.run (x : WithLogT σ m α) : m (WithLog' σ α) := x

instance [Monad m] : Monad (WithLogT σ m) where
  pure x := WithLogT.mk (pure {log := [], val := x})
  bind result next := WithLogT.mk do
    let {log := thisOut, val := thisRes} ← result
    let {log := nextOut, val := nextRes} ← next thisRes
    pure {log := thisOut ++ nextOut, val := nextRes}

class MonadWithLog (σ : outParam (Type u)) (m: Type u → Type v) :
    Type (max (u+1) v) where
  ok (x : β) : m β
  save :  σ → m PUnit
open MonadWithLog (ok save)

instance [Monad m] : MonadLift m (WithLogT σ m) where
  monadLift action := WithLogT.mk do pure {log := [], val := (← action)}

instance [Monad m] : MonadLift (WithLog' σ) (WithLogT σ m) where
  monadLift action := WithLogT.mk (pure action)

instance [Monad m] : MonadWithLog σ (WithLogT σ m) where
  ok x := WithLogT.mk (return (okLog' x))
  save x := WithLogT.mk (return (saveLog' x))

instance [Monad m] : MonadWithLog σ (ExceptT ε (WithLogT σ m)) where
  ok x := return x
  save x := WithLogT.mk (pure ({log := [x], val := pure ()}))

instance [Monad m] : MonadExcept ε (WithLogT σ (ExceptT ε m)) where
  throw e := WithLogT.mk (throw e)
  tryCatch m handler :=
    WithLogT.mk <|
      tryCatch
        (WithLogT.run m)
        (fun e => WithLogT.run (handler e))

/-
write a program that combines logging and exceptions.
-/

open BinTree in
def cTree :=
  branch
    (branch
      (branch leaf "5" (branch leaf "3" leaf))
      "2"
      leaf)
    "4"
    (branch leaf "1" leaf)

open BinTree in
def dTree :=
  branch
    (branch
      (branch leaf "5" (branch leaf "3" leaf))
      "a"
      leaf)
    "4"
    (branch leaf "1" leaf)

inductive ConvErr where
  | notANat : String → ConvErr
deriving Repr

def convLogEven [Monad m] [MonadExcept ConvErr m] [MonadWithLog Nat m] (s : String) : m Nat := do
  match s.toNat? with
  | none => throw (.notANat s)
  | some n =>
      if n % 2 == 0 then
        save n
      else
        pure ()
      pure n

#eval BinTree.mapM (m := ExceptT ConvErr (WithLogT Nat Id)) convLogEven cTree
#eval BinTree.mapM (m := WithLogT Nat (ExceptT ConvErr Id)) convLogEven cTree
#eval BinTree.mapM (m := ExceptT ConvErr (WithLogT Nat Id)) convLogEven dTree
#eval BinTree.mapM (m := WithLogT Nat (ExceptT ConvErr Id)) convLogEven dTree

---- TODO : Exercises

/- 6.2.6.3. Counting Files -/

/-
Modify doug's monad with StateT such that it counts the number of directories and files seen. At the end of execution, it should display a report like:

  Viewed 38 files in 5 directories.
-/

/- 6.3. Ordering Monad Transformers -/

def countLetters'' [Monad m] [MonadState LetterCounts m] [MonadExcept Err2 m]
    (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err2 Id)
abbrev M2 := ExceptT Err2 (StateT LetterCounts Id)

#eval countLetters'' (m := M1) "hello" ⟨0,0⟩ -- Except.ok ((), { vowels := 2, consonants := 3 })
#eval countLetters'' (m := M2) "hello" ⟨0,0⟩ -- (Except.ok (), { vowels := 2, consonants := 3 })

#eval countLetters'' (m := M1) "hello!" ⟨0, 0⟩ -- Except.error (Err2.notALetter '!')
#eval countLetters'' (m := M2) "hello!" ⟨0, 0⟩ -- (Except.error (Err2.notALetter '!'), { vowels := 2, consonants := 3 })

def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err2 m]
    (str : String) : m Unit :=
  try
    countLetters'' str
  catch _ =>
    countLetters'' "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0,0⟩ -- Except.ok ((), { vowels := 2, consonants := 3 })
#eval countWithFallback (m := M2) "hello" ⟨0,0⟩ -- (Except.ok (), { vowels := 2, consonants := 3 })

#eval countWithFallback (m := M1) "hello!" ⟨0,0⟩ -- Except.ok ((), { vowels := 2, consonants := 6 })
#eval countWithFallback (m := M2) "hello!" ⟨0,0⟩ -- (Except.ok (), { vowels := 4, consonants := 9 })

/- 6.3.2. Exercises -/

---- TODO : Exercises

/-
Check that ReaderT and StateT commute by expanding their definitions and reasoning about the resulting types.

Do ReaderT and ExceptT commute? Check your answer by expanding their definitions and reasoning about the resulting types.

Construct a monad transformer ManyT based on the definition of Many, with a suitable Alternative instance. Check that it satisfies the Monad contract.

Does ManyT commute with StateT? If so, check your answer by expanding definitions and reasoning about the resulting types. If not, write a program in ManyT (StateT σ Id) and a program in StateT σ (ManyT Id). Each program should be one that makes more sense for the given ordering of monad transformers.
-/

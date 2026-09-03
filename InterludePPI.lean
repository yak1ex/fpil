/- Interlude: Propositions, Proofs, and Indexing -/

def woodlandCritters : List String :=
  ["headgehog", "deer", "snail" ]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

/-
def oops := woodlanCritters[3]  -- failed to prove index is valid,
-/

/- Propositions and Proofs -/

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

/-
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl -- Type mismatch
-/

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo' : OnePlusOneIsTwo := rfl

/- Tactics -/

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by
  decide

/- Connectives -/

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

theorem andImpliedsOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a

theorem onePlusOneOrLessThan : 1 +1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide

/- Evidence as Arguments -/

/-
def third' (xs : List α) : α := xs[2] -- failed to prove index is valid
-/

def third (xs : List α) (h : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by decide)  -- "snail"

/- Indexing Without Evidence -/

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters  -- some "snail"
#eval thirdOption ["only", "two"]  -- none
#eval woodlandCritters[1]!  -- "deer"

/- Messages You May Meet -/

/-
#eval third ["rabiit"] (by decide)  -- Tactic `decide` proved that the proposition (snip) is false
-/

/-
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp -- `simp` made no progress
-/

/- Exercises -/
theorem twoPlusThreeIsFive : 2 + 3 = 5 := by rfl
theorem fifteenMinusEightIsSeven : 15 - 8 = 7 := by rfl
theorem helloWorld : "Hello, ".append "World!" = "Hello, World!" := by rfl
-- theorem fiveLessThanEighteen : 5 < 18 := by rfl
-- reflexivity is not enough to prove this,
-- because lhs and rhs are not definitionally equal,
-- but `decide` can do it

theorem twoPlusThreeIsFive' : 2 + 3 = 5 := by decide
theorem fifteenMinusEightIsSeven' : 15 - 8 = 7 := by decide
theorem helloWorld' : "Hello, ".append "World!" = "Hello, World!" := by decide
theorem fiveLessThanEighteen' : 5 < 18 := by decide

def listWithSixElements : List Nat := [1, 2, 3, 4, 5, 6]
def fifth (xs : List α) (h : xs.length > 4) : α := xs[4]
#eval fifth listWithSixElements (by decide)  -- 5

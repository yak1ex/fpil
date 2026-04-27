/- Interlude: Propositions, Proofs, and Indexing -/

def woodlanCritters : List String :=
  ["headgehog", "deer", "snail" ]

def hedgehog := woodlanCritters[0]
def deer := woodlanCritters[1]
def snail := woodlanCritters[2]

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

#eval third woodlanCritters (by decide)  -- "snail"

/- Indexing Without Evidence -/

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlanCritters  -- some "snail"
#eval thirdOption ["only", "two"]  -- none
#eval woodlanCritters[1]!  -- "deer"

/- Messages You May Meet -/

/-
#eval third ["rabiit"] (by decide)  -- Tactic `decide` proved that the proposition (snip) is false
-/

/-
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp -- `simp* made no progress
-/

/- 6. Monad Transformers -/

/- 6.1. Combining IO and Reader -/

/- 6.1.4. Exercises -/

/- 6.1.4.2. Starting Directory as Argument -/

-- from chapter3.lean
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))


structure Config where
  useASCII : Bool := false
  showAll : Bool := false
  root : String := "."
  currentPrefix : String := ""

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

structure Count where
  fileCount : Nat := 0
  dirCount : Nat := 0

abbrev ConfigIO (α : Type) : Type := ReaderT Config (StateT Count IO) α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg

def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  do pure (← action cfg {}).fst
def usage : String :=
  "Usage: doug [--ascii] [-a] [root]
Options:
\t--ascii\tUse ASCII characters to display the directory structure
\t-a\tShow all files and dirs including ones beginning with \".\"
\troot\tSpecify the root folder (default: the current folder)"

def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | x :: xs =>
    match configFromArgs xs with
    | none => none
    | some cfg =>
      match x with
      | "--ascii" => some {cfg with useASCII := true}
      | "-a" => some {cfg with showAll := true}
      | root => some {cfg with root := root }

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    if (← read).showAll || ! name.startsWith "." then
      pure (some (if (← path.isDir) then .dir name else .file name))
    else pure none

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def showFileName (file : String) : ConfigIO Unit := do
  let count ← get
  set {count with fileCount := count.fileCount + 1}
  IO.println s!"{(← read).currentPrefix}{(← read).preFile} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  let count ← get
  set {count with dirCount := count.dirCount + 1}
  IO.println s!"{(← read).currentPrefix}{(← read).preFile} {dir}/"

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action

partial def dirTree (path : System.FilePath) (showStat : Bool) : ConfigIO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    withReader (·.inDirectory)
      (doList (contents.qsort dirLT).toList fun d =>
        dirTree d.path false)
  if showStat then
    let count ← get
    IO.println s!"Viewed {count.fileCount} files in {count.dirCount} directories"

def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    let root ← if config.root == "." then IO.currentDir else pure ⟨config.root⟩
    (dirTree root true).run config
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1

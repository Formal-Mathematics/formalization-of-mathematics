import Lean

def template (nm : String) : String := s!"import LeanSlides

#set_pandoc_options \"-V\" \"theme=white\"

#slides {nm} /-!

# {nm}

-/"

def main (args : List String) : IO Unit := do 
  let some fname := args[0]? | IO.println "Usage: lake exe new_file {name}"
  let fnamel := fname ++ ".lean"
  let fnamel := System.FilePath.mk fnamel
  let fpath := "FormalizationOfMathematics" / fnamel
  if (← fpath.pathExists) then 
    IO.println s!"File {fname}.lean already exists."
    return
  IO.FS.withFile fpath .write fun handle => 
    handle.putStrLn (template fname)
  IO.FS.withFile "FormalizationOfMathematics.lean" .append fun handle => 
    handle.putStrLn <| "import FormalizationOfMathematics." ++ fname
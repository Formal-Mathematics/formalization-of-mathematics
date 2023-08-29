import Lean

def template (nm : String) : String := s!"import LeanSlides

#set_pandoc_options \"-V\" \"theme=white\"

#slides {nm} /-!

# {nm}

-/"

def main (args : List String) : IO Unit := do 
  let some fname := args[0]? | IO.println "Usage"
  let fnamel := fname ++ ".lean"
  let fnamel := System.FilePath.mk fnamel
  let fpath := "FormalizationOfMathematics" / fnamel
  let fileExists ← show IO Bool from do
    try 
      let _ ← IO.FS.readFile fpath
      return true
    catch _ => 
      return false
  if fileExists then 
    IO.println "File already exists."
    return
  IO.FS.withFile fpath .write fun handle => 
    handle.putStrLn (template fname)
  IO.FS.withFile "FormalizationOfMathematics.lean" .append fun handle => 
    handle.putStrLn <| "import FormalizationOfMathematics." ++ fname
import Lean
import Mathlib.Tactic
import Std.Tactic.TryThis

open Lean

namespace GPT 

inductive Role where | user | assistant | system
deriving ToJson, FromJson

structure Message where
  role : Role
  content : String
deriving ToJson, FromJson

def getJsonResponse (req : Json) : IO Json := do
  let some apiKey ← IO.getEnv "OPENAI_API_KEY" | 
    throw <| .userError "Failed to fetch OpenAI API key"
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #[ 
      "https://api.openai.com/v1/chat/completions", 
      "-H", "Content-Type: application/json",
      "-H", "Authorization: Bearer " ++ apiKey, 
      "--data-binary", "@-"]
    stdin := .piped
    stderr := .piped
    stdout := .piped
  }
  let (stdin,child) ← child.takeStdin
  stdin.putStr <| toString req
  stdin.flush
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode != 0 then throw <| .userError err
  let out ← IO.ofExcept stdout.get
  match Json.parse out with
  | .ok json => return json
  | .error err => throw <| .userError s!"{err}\n{req}"

def getResponses (msgs : Array Message) (n : Nat := 1) : IO (Array GPT.Message) := do
  let req : Json := 
    Json.mkObj [
      ("model", "gpt-4"),
      ("messages", toJson <| msgs),
      ("n", n)
    ]
  let jsonResponse ← getJsonResponse req
  let .ok choices := jsonResponse.getObjValAs? (Array Json) "choices" | 
    throw <| .userError s!"Failed to parse choices as array:
{jsonResponse}"
  let .ok choices := choices.mapM fun j => j.getObjValAs? GPT.Message "message" | 
    throw <| .userError s!"Failed to parse messages:
{choices}"
  return choices

def getResponse (msgs : Array Message) : IO GPT.Message := do
  let msgs ← getResponses msgs
  let some msg := msgs[0]? | 
    throw <| .userError s!"No messages were returned." 
  return msg
 
end GPT

open Lean Elab Tactic Meta in
elab "help!?" : tactic => do 
  let goalState ← ppGoal (← getMainGoal)
  let res ← GPT.getResponse #[
    {
      role := .system
      content := "You are an expert mathematician and an expert with the Lean4 interactive proof assistatnt.
The user will provide you with their current goal state, which includes the goal context and the goal itself.
Your task is to provide the next tactic. 
Don't add any other text, just the tactic.
Remember that this is Lean4, not Lean3, so:
1. Tactics do not end with a comma or a period.
2. rewrite have the following syntax `rw [h1, h2, ...]`

If you are unsure about what tactic to provide next, but you have an idea for what the user should do, then say:

\"[IDEA] Put your idea here.\"
"
    },
    {
      role := .user
      content := toString goalState
    }
  ] 
  let res := res.content
  match Parser.runParserCategory (← getEnv) `tactic res with
  | .ok stx => 
    Std.Tactic.TryThis.addSuggestion (← getRef) (⟨stx⟩ : TSyntax `tactic)
  | .error _ => 
    logInfoAt (← getRef) m!"{res}"

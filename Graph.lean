import Mathlib

open Lean Meta Elab Command

-- generalized
/-- Write an import graph, represented as a an array of `NameMap`s to the ".dot" graph format.
  If `("style1", graph1)` is in `graphs`, then the edges in `graph1` will be labeled with `[style1]`.
  Example: `asStyledDotGraph #[("", graph1), ("style=dashed", graph2)]` -/
def asStyledDotGraph [ForIn Id α Name] (graphs : Array (String × NameMap α))
    (header := "import_graph") : String := Id.run do
  let mut lines := #[s!"digraph \"{header}\" " ++ "{"]
  for (style, graph) in graphs do
    let label := if style == "" then "" else s!" [{style}]"
    for (n, is) in graph do
      for i in is do
        lines := lines.push s!"  \"{n}\" -> \"{i}\"{label};"
  lines := lines.push "}"
  return "\n".intercalate lines.toList

/-- Write an import graph, represented as a a `NameMap` to the ".dot" graph format. -/
def asDotGraph [ForIn Id α Name] (graph : NameMap α) (header := "import_graph") : String :=
  asStyledDotGraph #[("", graph)] header

-- slightly modified from elsewhere
private def isBlackListed (declName : Name) : CoreM Bool := do
  if declName.getRoot == `Lean then return true
  let env ← getEnv
  pure $ declName.isInternal'
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

namespace Lean

instance (α : Type u) (cmp : α → α → Ordering) : Singleton α (RBTree α cmp) where
  singleton x := .insert ∅ x

instance : Singleton Name NameSet where
  singleton x := .insert ∅ x

instance (α : Type u) (cmp : α → α → Ordering) : Insert α (RBTree α cmp) where
  insert x xs := xs.insert x

instance : Insert Name NameSet where
  insert x xs := xs.insert x

/-- Given `t : RBMap α β` where the value type `β` implements `Singleton γ β` and `Insert γ β`
instances.
For example, `β = List γ` or `β = RBTree γ`. Then `t.insert2 x (y : γ)` inserts `y` at key `x` into
`t`. -/
def RBMap.insert2 [Singleton γ β] [Insert γ β] {cmp : α → α → Ordering} (t : RBMap α β cmp)
    (x : α) (y : γ) : RBMap α β cmp :=
  match t.find? x with
  | some ys => t.insert x (Insert.insert y ys)
  | none    => t.insert x {y}

/-- `RBMap.insert2` specialized to `NameMap`. -/
def NameMap.insert2 [Singleton γ β] [Insert γ β] (t : NameMap β)
    (x : Name) (y : γ) : NameMap β :=
  RBMap.insert2 t x y

end Lean

/-- this instance causes a cycle -/
def blacklisted : NameSet :=
  .ofList [`CategoryTheory.locallySmall_self]

/--
Retrieve all names in the environment satisfying a predicate as a NameSet.
-/
def allNamesAsSet (p : Name → Bool) : CoreM NameSet := do
  (← getEnv).constants.foldM (init := {}) fun names n _ => do
    if p n && !(← isBlackListed n) then
      return names.insert n
    else
      return names

-- set_option profiler true
-- set_option trace.profiler true
def getClassInstanceGraph (full := true) : MetaM (NameMap NameSet) := do
  let classes := classExtension.getState (← getEnv) |>.outParamMap.toList.map (·.1)
  let classes : List (Name × List Name) ← classes.filterMapM fun nm => do
    forallTelescope (← inferType (← mkConstWithLevelParams nm)) fun args _ => do
      unless full || args.size == 1 do return none
      let ldecls ← args.mapM (·.fvarId!.getDecl)
      let bis := ldecls.map (·.binderInfo)
      unless bis.toList.count .default == 1 && bis[0]? == some .default &&
        ldecls[0]!.type.isSort do return none
      let tgts := ldecls.toList.drop 1 |>.map (·.type.getAppFnArgs.1)
      return some (nm, tgts)
  let argumentGraph : NameMap NameSet := classes.foldl (init := {}) fun r (src, tgts) =>
    r.insert src <| .ofList tgts
  let classes : NameSet := .ofList <| classes.map (·.1)
  let instances := instanceExtension.getState (← getEnv) |>.instanceNames.toList.map (·.1)
  let instances : List (Name × List Name × Name) ← instances.filterMapM fun nm => do
    forallTelescope (← inferType (← mkConstWithLevelParams nm)) fun args ty => do
      unless args.size ≥ 2 do return none
      unless full || args.size == 2 do return none
      let typeVar := args[0]!
      let (targetClass, targetClassArgs) := ty.getAppFnArgs
      unless classes.contains targetClass do return none
      unless targetClassArgs[0]? == some typeVar do return none
      if blacklisted.contains nm then return none
      let mut srcs := []
      let mut dupes : NameSet := {}
      for arg in args.toList.drop 1 do
        let (sourceClass, sourceClassArgs) := (← inferType arg).getAppFnArgs
        unless classes.contains sourceClass do return none
        unless sourceClassArgs[0]? == some typeVar do return none
        srcs := sourceClass::srcs
        dupes := dupes ++ (argumentGraph.find? sourceClass).get!
      let sources := srcs.filter (!dupes.contains ·)
      return (nm, sources, targetClass)
  let instanceGraph : NameMap NameSet := instances.foldl (init := {}) fun r (_, src, tgt) =>
    if src.length == 1 then r.insert2 src.head! tgt else r
  IO.FS.writeFile "classes.dot" <| asStyledDotGraph #[("", instanceGraph), ("style=dashed", argumentGraph)] "instance_graph"
  --logInfo m!"classes with 1 type parameter: {classes.size}"
  --logInfo m!"instances between these classes: {instances.length}"
  -- logInfo m!"classes: {classes}"
  --logInfo m!"forgetful instances with 1 source class: {instanceGraph.size}"
  --logInfo m!"argument instances: {argumentGraph.size}"
  -- logInfo m!"instances: {instances}"
  --logInfo m!"{asStyledDotGraph #[("", instanceGraph), ("style=dashed", argumentGraph)] "instance_graph"}"
  --logInfo m!"instances with more than 1 source: {instances.filter (·.2.1.length > 1)}"
  return instanceGraph
-- #check SemilinearEquivClass

--set_option profiler true

--run_cmd liftCoreM <| MetaM.run' <| do
--  getClassInstanceGraph
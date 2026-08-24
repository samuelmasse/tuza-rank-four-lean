import TuzaRankFour.Certificates.FromBinaryLRAT

/-!
# Checkpointed proof-producing LRAT import

Mathlib's LRAT importer represents a derivation as a shared expression DAG.
For large traces, a single final theorem can nevertheless make kernel checking
retain too much of that DAG at once.  This importer periodically packages the
currently live derived clauses into a balanced conjunction theorem.  Later
LRAT steps refer to projections of that named theorem, so each checkpoint
limits the proof-expression segment that the kernel must retain while all
certificate reasoning remains an ordinary proof term.
-/

open Lean Elab Command Term
open Std.Internal

namespace TuzaRankFour.Certificates

deriving instance Inhabited for Mathlib.Tactic.Sat.Clause

private def loadBinaryLRATText (proofPath : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile proofPath
  let actions ← IO.ofExcept
    (Std.Tactic.BVDecide.LRAT.parseLRATProof bytes)
  return Std.Tactic.BVDecide.LRAT.lratProofToString actions

private def clauseProofType (ctx : Expr)
    (clause : Mathlib.Tactic.Sat.Clause) : Expr :=
  mkApp2 (mkConst ``Sat.Fmla.proof) ctx clause.expr

private partial def bundleType (ctx : Expr)
    (entries : Array (Nat × Mathlib.Tactic.Sat.Clause))
    (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty checkpoint bundle"
  | 1 => clauseProofType ctx entries[start]!.2
  | length =>
      let middle := start + length / 2
      mkApp2 (mkConst ``And)
        (bundleType ctx entries start middle)
        (bundleType ctx entries middle stop)

private partial def bundleValue (ctx : Expr)
    (entries : Array (Nat × Mathlib.Tactic.Sat.Clause))
    (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty checkpoint bundle"
  | 1 => entries[start]!.2.proof
  | length =>
      let middle := start + length / 2
      let leftType := bundleType ctx entries start middle
      let rightType := bundleType ctx entries middle stop
      mkApp4 (mkConst ``And.intro) leftType rightType
        (bundleValue ctx entries start middle)
        (bundleValue ctx entries middle stop)

private partial def bundleProjection (ctx : Expr)
    (entries : Array (Nat × Mathlib.Tactic.Sat.Clause))
    (proof : Expr) (start stop index : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty checkpoint bundle"
  | 1 => proof
  | length =>
      let middle := start + length / 2
      let leftType := bundleType ctx entries start middle
      let rightType := bundleType ctx entries middle stop
      if index < middle then
        bundleProjection ctx entries
          (mkApp3 (mkConst ``And.left) leftType rightType proof)
          start middle index
      else
        bundleProjection ctx entries
          (mkApp3 (mkConst ``And.right) leftType rightType proof)
          middle stop index

private def addCheckpoint (baseName : Name) (checkpointIndex : Nat)
    (ctx : Expr)
    (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause)
    (derived : Std.HashSet Nat) : MetaM
      (Std.HashMap Nat Mathlib.Tactic.Sat.Clause) := do
  let ids := derived.toArray.qsort (· < ·)
  if ids.isEmpty then
    return db
  let entries := ids.map fun id => (id, db[id]!)
  let checkpointName := Name.mkStr baseName s!"checkpoint{checkpointIndex}"
  addDecl <| Declaration.thmDecl {
    name := checkpointName
    levelParams := []
    type := bundleType ctx entries 0 entries.size
    value := bundleValue ctx entries 0 entries.size
  }
  let checkpoint := Lean.mkConst checkpointName
  let mut updated := db
  for index in [:entries.size] do
    let (id, clause) := entries[index]!
    let proof := bundleProjection ctx entries checkpoint 0 entries.size index
    updated := updated.insert id { clause with proof := proof }
  return updated

private def addBundleDeclaration (name : Name) (ctx : Expr)
    (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause)
    (derived : Std.HashSet Nat) : MetaM Unit := do
  let ids := derived.toArray.qsort (· < ·)
  if ids.isEmpty then
    throwError "cannot export an empty derived-clause checkpoint"
  let entries := ids.map fun id => (id, db[id]!)
  addDecl <| Declaration.thmDecl {
    name
    levelParams := []
    type := bundleType ctx entries 0 entries.size
    value := bundleValue ctx entries 0 entries.size
  }

private def decodeLiteralExpr (literal : Expr) : Except String Int := do
  let constructor := literal.getAppFn.constName?
  let some variableIndex := literal.appArg!.rawNatLit?
    | throw "checkpoint contains a non-numeral SAT literal"
  match constructor with
  | some ``Sat.Literal.pos => return Int.ofNat (variableIndex + 1)
  | some ``Sat.Literal.neg => return -Int.ofNat (variableIndex + 1)
  | _ => throw "checkpoint contains a malformed SAT literal"

private partial def decodeClauseExpr (clause : Expr) : Except String (Array Int) := do
  if clause.isConstOf ``Sat.Clause.nil then
    return #[]
  unless clause.isAppOfArity ``Sat.Clause.cons 2 do
    throw "checkpoint contains a malformed SAT clause"
  let literal ← decodeLiteralExpr clause.appFn!.appArg!
  let rest ← decodeClauseExpr clause.appArg!
  return #[literal] ++ rest

private partial def collectBundleClauses (ctx bundleType bundleProof : Expr) :
    Except String (Array Mathlib.Tactic.Sat.Clause) := do
  if bundleType.isAppOfArity ``And 2 then
    let leftType := bundleType.appFn!.appArg!
    let rightType := bundleType.appArg!
    let leftProof := mkApp3 (Lean.mkConst ``And.left) leftType rightType bundleProof
    let rightProof := mkApp3 (Lean.mkConst ``And.right) leftType rightType bundleProof
    return (← collectBundleClauses ctx leftType leftProof) ++
      (← collectBundleClauses ctx rightType rightProof)
  unless bundleType.isAppOfArity ``Sat.Fmla.proof 2 do
    throw "checkpoint leaf is not a formula-clause proof"
  let formula := bundleType.appFn!.appArg!
  unless formula == ctx do
    throw "checkpoint formula does not match the requested base formula"
  let clauseExpr := bundleType.appArg!
  let literals ← decodeClauseExpr clauseExpr
  return #[{ lits := literals, expr := clauseExpr, proof := bundleProof }]

private def parseClauseIds (source : String) : Except String (Array Nat) := do
  let mut ids := #[]
  for field in source.split (·.isWhitespace) do
    if field.isEmpty then
      continue
    let some id := field.toNat?
      | throw s!"malformed checkpoint clause id `{field}`"
    ids := ids.push id
  return ids

private inductive SegmentResult
  | checkpoint
      (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause)
      (derived : Std.HashSet Nat)
  | refutation (proof : Expr)

private def buildSegmentProof (clauses : Array (Array Int))
    (ctx expanded : Expr) (steps : Array Mathlib.Tactic.Sat.LRATStep)
    (prior : Option (Array Nat × Expr)) : MetaM SegmentResult := do
  let selfProof := mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db :=
    (Mathlib.Tactic.Sat.buildClauses clauses ctx 0 clauses.size expanded
      selfProof default).2
  let mut derived : Std.HashSet Nat := {}
  if let some (ids, priorProof) := prior then
    let priorType ← Meta.inferType priorProof
    let priorClauses ← IO.ofExcept (collectBundleClauses ctx priorType priorProof)
    unless ids.size = priorClauses.size do
      throwError "checkpoint id count does not match its clause bundle"
    for index in [:ids.size] do
      let id := ids[index]!
      db := db.insert id priorClauses[index]!
      derived := derived.insert id
  for step in steps do
    match step with
    | .del ids =>
        db := ids.foldl (·.erase ·) db
        derived := ids.foldl (·.erase ·) derived
    | .add id literals hints =>
        let clauseExpr := Mathlib.Tactic.Sat.buildClause literals
        match Mathlib.Tactic.Sat.buildProofStep db literals hints ctx clauseExpr with
        | .error message => throwError message
        | .ok proof =>
            if literals.isEmpty then
              return .refutation proof
            db := db.insert id {
              lits := literals
              expr := clauseExpr
              proof
            }
            derived := derived.insert id
  return .checkpoint db derived

private def addSegmentDeclaration (name : Name) (ctx : Expr)
    (result : SegmentResult) : MetaM Unit := do
  match result with
  | .checkpoint db derived => addBundleDeclaration name ctx db derived
  | .refutation proof =>
      addDecl <| Declaration.thmDecl {
        name
        levelParams := []
        type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx
          (Mathlib.Tactic.Sat.buildClause #[])
        value := proof
      }

private def buildCheckpointedProof
    (baseName : Name) (clauses : Array (Array Int))
    (ctx expanded : Expr) (steps : Array Mathlib.Tactic.Sat.LRATStep)
    (checkpointFrequency : Nat) : MetaM Expr := do
  if checkpointFrequency = 0 then
    throwError "checkpoint frequency must be positive"
  let selfProof := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db :=
    (Mathlib.Tactic.Sat.buildClauses clauses ctx 0 clauses.size expanded
      selfProof default).2
  let mut derived : Std.HashSet Nat := {}
  let mut additionsSinceCheckpoint := 0
  let mut checkpointIndex := 0
  for step in steps do
    match step with
    | .del ids =>
        db := ids.foldl (·.erase ·) db
        derived := ids.foldl (·.erase ·) derived
    | .add id literals hints =>
        let clauseExpr := Mathlib.Tactic.Sat.buildClause literals
        match Mathlib.Tactic.Sat.buildProofStep db literals hints ctx clauseExpr with
        | .error message => throwError message
        | .ok proof =>
            if literals.isEmpty then
              return proof
            db := db.insert id {
              lits := literals
              expr := clauseExpr
              proof
            }
            derived := derived.insert id
            additionsSinceCheckpoint := additionsSinceCheckpoint + 1
            if additionsSinceCheckpoint = checkpointFrequency then
              checkpointIndex := checkpointIndex + 1
              db ← addCheckpoint baseName checkpointIndex ctx db derived
              additionsSinceCheckpoint := 0
  throwError "failed to prove empty clause"

/-- Import a binary LRAT proof as a checkpointed ordinary proof term for the
empty clause of an already named DIMACS formula. -/
elab "checkpoint_lrat_core_proof_binary " n:ident ppSpace base:term:max ppSpace
    cnf:term:max ppSpace path:str ppSpace frequency:num : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let sourcePath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourcePath.parent
    | throwError "cannot compute source directory of `{sourcePath}`"
  let proofPath := sourceDirectory / path.getString
  let proofText ← loadBinaryLRATText proofPath
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let .success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    let .success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, proofText.startPos⟩
      | throwError "parse LRAT failed"
    let baseExpr ← elabTermEnsuringType base (mkConst ``Sat.Fmla)
    let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    let proof ← buildCheckpointedProof name clauses baseExpr expanded steps frequency.getNat
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := mkApp2 (mkConst ``Sat.Fmla.proof) baseExpr
        (Mathlib.Tactic.Sat.buildClause #[])
      value := proof
    }

/-- Check one initial LRAT segment.  If the segment derives the empty clause,
the declaration is a refutation; otherwise it is the balanced live-clause
checkpoint consumed by the next segment module. -/
elab "lrat_initial_segment_binary " n:ident ppSpace base:term:max ppSpace
    cnf:term:max ppSpace path:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let sourcePath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourcePath.parent
    | throwError "cannot compute source directory of `{sourcePath}`"
  let proofText ← loadBinaryLRATText (sourceDirectory / path.getString)
  liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let .success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    let .success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, proofText.startPos⟩
      | throwError "parse LRAT segment failed"
    let baseExpr ← elabTermEnsuringType base (Lean.mkConst ``Sat.Fmla)
    let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    let result ← buildSegmentProof clauses baseExpr expanded steps none
    addSegmentDeclaration name baseExpr result

/-- Check a later LRAT segment using the preceding live-clause checkpoint and
its sorted list of LRAT clause identifiers. -/
elab "lrat_segment_binary " n:ident ppSpace base:term:max ppSpace
    prior:term:max ppSpace ids:term:max ppSpace cnf:term:max ppSpace
    path:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let sourcePath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourcePath.parent
    | throwError "cannot compute source directory of `{sourcePath}`"
  let proofText ← loadBinaryLRATText (sourceDirectory / path.getString)
  liftTermElabM do
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let idSource ← unsafe evalTerm String (Lean.mkConst ``String) ids
    let clauseIds ← IO.ofExcept (parseClauseIds idSource)
    let .success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    let .success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, proofText.startPos⟩
      | throwError "parse LRAT segment failed"
    let baseExpr ← elabTermEnsuringType base (Lean.mkConst ``Sat.Fmla)
    let priorExpr ← elabTerm prior none
    synthesizeSyntheticMVarsNoPostponing
    let priorExpr ← instantiateMVars priorExpr
    let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    let result ← buildSegmentProof clauses baseExpr expanded steps
      (some (clauseIds, priorExpr))
    addSegmentDeclaration name baseExpr result

end TuzaRankFour.Certificates

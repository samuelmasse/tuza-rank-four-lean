import Mathlib.Tactic.Sat.FromLRAT
import Std.Tactic.BVDecide.LRAT.Parser

/-!
# Binary LRAT import

Mathlib's proof-producing LRAT importer accepts text.  `drat-trim` also emits
the standard compact binary LRAT representation.  This command decodes that
representation with Lean's LRAT parser and then hands the canonical text to
Mathlib's proof-producing importer.  The resulting declaration is an ordinary
kernel-checked proof term; native evaluation and `Lean.ofReduceBool` are not
used.
-/

open Lean Elab Command Term
open Std.Internal

namespace TuzaRankFour.Certificates

private def loadLRATText (proofPath : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile proofPath
  let actions ← IO.ofExcept
    (Std.Tactic.BVDecide.LRAT.parseLRATProof bytes)
  return Std.Tactic.BVDecide.LRAT.lratProofToString actions

private def appendDimacsClauses (cnf extra : String) : Except String String := do
  let header :: body := cnf.splitOn "\n"
    | throw "empty DIMACS input"
  let fields := (header.splitOn " ").filter (· != "")
  let [p, format, variables, clauseCount] := fields
    | throw "malformed DIMACS header"
  if p != "p" || format != "cnf" then
    throw "malformed DIMACS header"
  let some declared := clauseCount.toNat?
    | throw "non-numeric DIMACS clause count"
  let additions := (extra.splitOn "\n").filter (·.trimAscii.toString != "")
  let newHeader := s!"p cnf {variables} {declared + additions.length}"
  return String.intercalate "\n" (newHeader :: body) ++ "\n" ++ extra

elab "lrat_proof_binary " n:ident ppSpace cnf:term:max ppSpace path:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let srcPath := System.FilePath.mk (← getFileName)
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  let proofPath := srcDir / path.getString
  let lrat ← loadLRATText proofPath
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    Mathlib.Tactic.Sat.fromLRAT cnf lrat name

/-- Name a DIMACS formula so that several cube refutations can share it. -/
elab "dimacs_formula_binary " n:ident ppSpace cnf:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    addDecl <| Declaration.defnDecl {
      name
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
      hints := .regular 0
      safety := .safe
    }

/-- Import a binary LRAT refutation as a proof of the empty clause from a
previously named DIMACS formula. -/
elab "lrat_core_proof_binary " n:ident ppSpace base:term:max ppSpace
    cnf:term:max ppSpace path:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let srcPath := System.FilePath.mk (← getFileName)
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  let proofPath := srcDir / path.getString
  let lrat ← loadLRATText proofPath
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let Parsec.ParseResult.success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    let Parsec.ParseResult.success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
      | throwError "parse LRAT failed"
    let baseExpr ← elabTermEnsuringType base (mkConst ``Sat.Fmla)
    let expanded := Mathlib.Tactic.Sat.buildConj clauses 0 clauses.size
    let proof ← Mathlib.Tactic.Sat.buildProof clauses baseExpr expanded steps
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := mkApp2 (mkConst ``Sat.Fmla.proof) baseExpr
        (Mathlib.Tactic.Sat.buildClause #[])
      value := proof
    }

/-- Import a binary LRAT refutation of a named formula under an explicit list
of unit clauses.  This is the leaf theorem used by an exhaustive decision-tree
partition. -/
elab "lrat_cube_core_proof_binary " n:ident ppSpace base:term:max ppSpace
    cnf:term:max ppSpace extra:term:max ppSpace path:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let srcPath := System.FilePath.mk (← getFileName)
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  let proofPath := srcDir / path.getString
  let lrat ← loadLRATText proofPath
  liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let extra ← unsafe evalTerm String (mkConst ``String) extra
    let fullCnf ← IO.ofExcept (appendDimacsClauses cnf extra)
    let Parsec.ParseResult.success _ (_, baseClauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "parse base CNF failed"
    let Parsec.ParseResult.success _ (_, fullClauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, fullCnf.startPos⟩
      | throwError "parse augmented CNF failed"
    let Parsec.ParseResult.success _ steps :=
        Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, lrat.startPos⟩
      | throwError "parse LRAT failed"
    let baseExpr ← elabTermEnsuringType base (mkConst ``Sat.Fmla)
    let unitClauses := fullClauses.extract baseClauses.size fullClauses.size
    let ctx := unitClauses.foldl (fun formula clause =>
      mkApp2 (mkConst ``Sat.Fmla.and) formula
        (mkApp (mkConst ``Sat.Fmla.one)
          (Mathlib.Tactic.Sat.buildClause clause))) baseExpr
    let expanded := Mathlib.Tactic.Sat.buildConj fullClauses 0 fullClauses.size
    let proof ← Mathlib.Tactic.Sat.buildProof fullClauses ctx expanded steps
    addDecl <| Declaration.thmDecl {
      name
      levelParams := []
      type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx
        (Mathlib.Tactic.Sat.buildClause #[])
      value := proof
    }

end TuzaRankFour.Certificates

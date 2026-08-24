import TuzaRankFour.SemanticEncoding

/-!
# Compact semantic-witness import

The finite endpoint stores each packing or cover witness as a short list of
zero-based combinatorial indices.  This elaborator reads the compact binary
stream and installs ordinary Lean definitions.  Correctness does not depend
on trusting the elaborator: the generated modules prove in the kernel that
every decoded witness is valid and that the reconstructed formula is exactly
the independently imported DIMACS formula.
-/

open Lean Elab Command

namespace TuzaRankFour.Certificates

private structure Cursor where
  bytes : ByteArray
  offset : Nat

private def Cursor.readByte (cursor : Cursor) : Except String (UInt8 × Cursor) := do
  if h : cursor.offset < cursor.bytes.size then
    return (cursor.bytes[cursor.offset], { cursor with offset := cursor.offset + 1 })
  throw "unexpected end of semantic-witness stream"

private def Cursor.readVarNat (cursor : Cursor) : Except String (Nat × Cursor) := do
  let mut value := 0
  let mut shift := 0
  let mut current := cursor
  for _ in [:10] do
    let (byte, next) ← current.readByte
    let payload := byte.toNat &&& 0x7f
    value := value ||| (payload <<< shift)
    current := next
    if byte.toNat < 0x80 then
      return (value, current)
    shift := shift + 7
  throw "semantic-witness varint exceeds ten bytes"

private def expectedMagic : Array UInt8 :=
  #[0x54, 0x43, 0x55, 0x54, 0x30, 0x30, 0x30, 0x31]

private structure RawCut where
  packing : Bool
  indices : Array Nat

private structure RawBundle where
  order : Nat
  skeleton : Nat
  marked : Array Nat
  cuts : Array RawCut

private def parseBundle (bytes : ByteArray) : Except String RawBundle := do
  let mut cursor : Cursor := { bytes, offset := 0 }
  for expected in expectedMagic do
    let (actual, next) ← cursor.readByte
    unless actual == expected do
      throw "bad semantic-witness magic"
    cursor := next
  let (order, next) ← cursor.readVarNat
  cursor := next
  let (skeleton, next) ← cursor.readVarNat
  cursor := next
  let (markedCount, next) ← cursor.readVarNat
  cursor := next
  let mut marked := #[]
  for _ in [:markedCount] do
    let (index, next) ← cursor.readVarNat
    marked := marked.push index
    cursor := next
  let (cutCount, next) ← cursor.readVarNat
  cursor := next
  let mut cuts := #[]
  for _ in [:cutCount] do
    let (tag, next) ← cursor.readByte
    cursor := next
    unless tag == 0 || tag == 1 do
      throw s!"unknown semantic-witness tag {tag}"
    let (indexCount, next) ← cursor.readVarNat
    cursor := next
    let mut indices := #[]
    for _ in [:indexCount] do
      let (index, next) ← cursor.readVarNat
      indices := indices.push index
      cursor := next
    cuts := cuts.push { packing := tag == 0, indices }
  unless cursor.offset == bytes.size do
    throw "trailing bytes in semantic-witness stream"
  return { order, skeleton, marked, cuts }

private def mkListExpr (elementType : Expr) (items : Array Expr) : Expr :=
  items.foldr
    (fun item tail => mkApp3 (mkConst ``List.cons [Level.zero]) elementType item tail)
    (mkApp (mkConst ``List.nil [Level.zero]) elementType)

private def mkNatListExpr (items : Array Nat) : Expr :=
  mkListExpr (mkConst ``Nat) (items.map mkRawNatLit)

private def mkCutExpr (cut : RawCut) : Expr :=
  let constructor :=
    if cut.packing then
      ``TuzaRankFour.SemanticEncoding.Cut.packing
    else
      ``TuzaRankFour.SemanticEncoding.Cut.cover
  mkApp (mkConst constructor) (mkNatListExpr cut.indices)

private def addDefinition (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.defnDecl {
    name
    levelParams := []
    type
    value
    hints := .regular 0
    safety := .safe
  }

/-- Import a compact witness stream as two kernel-visible definitions. -/
elab "semantic_cut_bundle_binary " markedName:ident ppSpace cutsName:ident ppSpace
    orderSyntax:num ppSpace skeletonSyntax:num ppSpace path:str : command => do
  let sourcePath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourcePath.parent
    | throwError "cannot compute parent directory of `{sourcePath}`"
  let binaryPath := sourceDirectory / path.getString
  let bytes ← IO.FS.readBinFile binaryPath
  let bundle ← IO.ofExcept (parseBundle bytes)
  let expectedOrder := orderSyntax.getNat
  let expectedSkeleton := skeletonSyntax.getNat
  unless bundle.order == expectedOrder do
    throwError "semantic-witness order mismatch: expected {expectedOrder}, got {bundle.order}"
  unless bundle.skeleton == expectedSkeleton do
    throwError "semantic-witness skeleton mismatch: expected {expectedSkeleton}, got {bundle.skeleton}"
  unless bundle.marked.size == 4 do
    throwError "semantic-witness stream must contain exactly four marked triangles"
  let currentNamespace ← getCurrNamespace
  let markedDecl := currentNamespace ++ markedName.getId
  let cutsDecl := currentNamespace ++ cutsName.getId
  let listNat := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  let cutType := mkConst ``TuzaRankFour.SemanticEncoding.Cut
  let listCut := mkApp (mkConst ``List [Level.zero]) cutType
  liftTermElabM do
    addDefinition markedDecl listNat (mkNatListExpr bundle.marked)
    addDefinition cutsDecl listCut
      (mkListExpr cutType (bundle.cuts.map mkCutExpr))

private partial def collectFormulaChunks (clauses : Array (Array Int))
    (maximumSize start stop : Nat) : Array Expr :=
  if stop - start ≤ maximumSize then
    #[Mathlib.Tactic.Sat.buildConj clauses start stop]
  else
    let middle := start + (stop - start) / 2
    collectFormulaChunks clauses maximumSize start middle ++
      collectFormulaChunks clauses maximumSize middle stop

private partial def collectFormulaChunkRanges (maximumSize start stop : Nat) :
    Array (Nat × Nat) :=
  if stop - start ≤ maximumSize then
    #[(start, stop)]
  else
    let middle := start + (stop - start) / 2
    collectFormulaChunkRanges maximumSize start middle ++
      collectFormulaChunkRanges maximumSize middle stop

/-- Name the balanced DIMACS subtrees of bounded size.  The subtrees retain
the exact recursive shape used by Mathlib's LRAT importer, allowing a case
module to assemble formula satisfaction without normalizing one enormous
list equality. -/
elab "dimacs_formula_chunks " chunkPrefix:ident ppSpace maximumSizeSyntax:num ppSpace
    cnf:term:max : command => do
  let maximumSize := maximumSizeSyntax.getNat
  if maximumSize = 0 then
    throwError "formula chunk size must be positive"
  let currentNamespace ← getCurrNamespace
  liftTermElabM do
    let source ← unsafe Term.evalTerm String (mkConst ``String) cnf
    let .success _ (_, clauses) :=
        Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, source.startPos⟩
      | throwError "parse CNF failed"
    if clauses.isEmpty then
      throwError "empty CNF"
    let chunks := collectFormulaChunks clauses maximumSize 0 clauses.size
    for index in [:chunks.size] do
      let name := Name.mkStr currentNamespace s!"{chunkPrefix.getId}{index}"
      addDefinition name (mkConst ``Sat.Fmla) chunks[index]!

/-- Import the cut sublists aligned with `dimacs_formula_chunks`.  Direct
sublist declarations keep each kernel computation local instead of repeatedly
reducing `List.drop` across a large preceding witness stream. -/
elab "semantic_cut_slices_binary " chunkPrefix:ident ppSpace orderSyntax:num ppSpace
    skeletonSyntax:num ppSpace baseCountSyntax:num ppSpace maximumSizeSyntax:num
    ppSpace path:str : command => do
  let expectedOrder := orderSyntax.getNat
  let expectedSkeleton := skeletonSyntax.getNat
  let baseCount := baseCountSyntax.getNat
  let maximumSize := maximumSizeSyntax.getNat
  if maximumSize = 0 then
    throwError "cut slice size must be positive"
  let sourcePath := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourcePath.parent
    | throwError "cannot compute parent directory of `{sourcePath}`"
  let bytes ← IO.FS.readBinFile (sourceDirectory / path.getString)
  let bundle ← IO.ofExcept (parseBundle bytes)
  unless bundle.order == expectedOrder do
    throwError "semantic-witness order mismatch"
  unless bundle.skeleton == expectedSkeleton do
    throwError "semantic-witness skeleton mismatch"
  let ranges := collectFormulaChunkRanges maximumSize 0 (baseCount + bundle.cuts.size)
  let currentNamespace ← getCurrNamespace
  let cutType := mkConst ``TuzaRankFour.SemanticEncoding.Cut
  let listCut := mkApp (mkConst ``List [Level.zero]) cutType
  liftTermElabM do
    for index in [:ranges.size] do
      let (start, stop) := ranges[index]!
      let cutStart := start - baseCount
      let cutStop := stop - baseCount
      let slice := bundle.cuts.extract cutStart cutStop
      let name := Name.mkStr currentNamespace s!"{chunkPrefix.getId}{index}"
      addDefinition name listCut (mkListExpr cutType (slice.map mkCutExpr))

end TuzaRankFour.Certificates

import Std.Tactic.BVDecide.LRAT.Parser

open Std.Tactic.BVDecide

private def convertOne (src dst : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile src
  let actions ← IO.ofExcept (LRAT.parseLRATProof bytes)
  LRAT.dumpLRATProof dst actions true
  let replay ← LRAT.loadLRATProof dst
  unless replay == actions do
    throw <| IO.userError s!"binary LRAT round trip failed for {src}"

def main (args : List String) : IO Unit := do
  let [srcDirName, dstDirName] := args
    | throw <| IO.userError "usage: convert_lrat_binary <source-directory> <destination-directory>"
  let srcDir := System.FilePath.mk srcDirName
  let dstDir := System.FilePath.mk dstDirName
  IO.FS.createDirAll dstDir
  let entries ← srcDir.readDir
  let entries := entries.qsort (fun a b => a.fileName < b.fileName)
  for entry in entries do
    if entry.path.extension == some "lrat" then
      let dst := dstDir / s!"{entry.fileName.dropRight 5}.lratb"
      convertOne entry.path dst
      IO.println s!"{entry.fileName} -> {dst.fileName}"

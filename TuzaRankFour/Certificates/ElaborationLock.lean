import Lean

/-!
# Bounded-memory certificate elaboration

Generated certificate modules are individually modest enough for hosted
verification, but Lake can elaborate many independent modules concurrently.
This cross-process lock keeps only one memory-heavy certificate command or
decision procedure active at a time.  It affects build scheduling only: the
resulting declarations remain ordinary kernel-checked proof terms.
-/

open Lean Elab Command

namespace TuzaRankFour.Certificates

/-- Run a memory-heavy elaboration action under a project-wide OS file lock. -/
def withCertificateElaborationLock
    [Monad m] [MonadFinally m] [MonadLiftT IO m] (act : m α) : m α := do
  let projectDirectory ← IO.Process.getCurrentDir
  -- Comparator's Landrun sandbox exposes `.lake/build` as the project's
  -- writable build area; the `.lake` root itself may be read-only.
  let lakeBuildDirectory := projectDirectory / ".lake" / "build"
  IO.FS.createDirAll lakeBuildDirectory
  let handle ← IO.FS.Handle.mk
    (lakeBuildDirectory / "tuza-certificate-elaboration.lock") .append
  handle.lock
  try
    act
  finally
    handle.unlock

/--
Elaborate a sequence of declarations while holding the certificate lock for
the entire sequence.  Keeping the lock across a generated module's related
theorems prevents several waiting processes from each retaining a half-built
proof environment.
-/
syntax (name := certificateLockedCommand)
  "certificate_locked" ppLine "{" ppLine command* ppLine "}" : command

elab_rules : command
  | `(certificate_locked { $commands:command* }) =>
      withCertificateElaborationLock do
        for command in commands do
          elabCommand command

end TuzaRankFour.Certificates

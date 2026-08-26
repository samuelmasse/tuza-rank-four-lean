import Lean

/-!
# Bounded-memory certificate elaboration

Generated certificate modules are individually modest enough for hosted
verification, but Lake can elaborate many independent modules concurrently.
This cross-process lock pool keeps at most two memory-heavy certificate
commands or decision procedures active at a time.  It affects build scheduling
only: the resulting declarations remain ordinary kernel-checked proof terms.
-/

open Lean Elab Command

namespace TuzaRankFour.Certificates

private partial def acquireCertificateElaborationSlot
    (handles : Array IO.FS.Handle) : IO IO.FS.Handle := do
  for handle in handles do
    if ← handle.tryLock then
      return handle
  IO.sleep 25
  acquireCertificateElaborationSlot handles

/-- Run a memory-heavy elaboration action in a two-worker, project-wide pool. -/
def withCertificateElaborationLock
    [Monad m] [MonadFinally m] [MonadLiftT IO m] (act : m α) : m α := do
  let projectDirectory ← IO.Process.getCurrentDir
  -- Comparator's Landrun sandbox exposes `.lake/build` as the project's
  -- writable build area; the `.lake` root itself may be read-only.
  let lakeBuildDirectory := projectDirectory / ".lake" / "build"
  IO.FS.createDirAll lakeBuildDirectory
  let handles ← #[0, 1].mapM fun slot => IO.FS.Handle.mk
    (lakeBuildDirectory / s!"tuza-certificate-elaboration-{slot}.lock") .append
  let handle ← acquireCertificateElaborationSlot handles
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

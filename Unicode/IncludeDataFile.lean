import Lean
import Std.Data.HashMap

namespace Unicode

open Lean System IO Lean.Elab.Term

syntax (name := includeDataFile) "include_data_file" str : term

@[termElab includeDataFile] def includeDataFileImp : TermElab := λ stx expectedType? => do
  let str := stx[1].isStrLit?.get!
  let path := FilePath.mk str
  if ←path.pathExists then
    if ←path.isDir then
      throwError s!"{str} is a directory"
    else
      let mut stxs := #[]
      for line in (← FS.lines path).filter (· ≠ "") do
        IO.println line
        let splits := line.splitOn ";" |>.map String.trim
        stxs := stxs.push (← `(($(Syntax.mkStrLit (splits.get! 0)), $(Syntax.mkStrLit (splits.get! 2)))))
      -- let stxs ← (← FS.lines path).filter (· ≠ "")
      --   |>.mapM λ line =>
      --     let splits := line.splitOn ";" |>.map String.trim
      --     `(($(Syntax.mkStrLit (splits.get! 0)), $(Syntax.mkStrLit (splits.get! 2))))
      elabTerm (←`([$[$stxs],*].foldl (fun m (k, v) => m.insert k v) Std.HashMap.empty)) none
  else
    throwError s!"\"{str}\" does not exist as a file"

end Unicode

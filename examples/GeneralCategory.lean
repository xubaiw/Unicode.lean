import Unicode.General.GeneralCategory

open Unicode

def main : IO Unit := do
  IO.println $ getGeneralCategory 'a'
  IO.println $ getGeneralCategory '←'
  IO.println $ getGeneralCategory '-'
  IO.println $ getGeneralCategory $ Char.mk 0x10ead (by decide)
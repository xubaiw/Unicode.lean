import Unicode

open Unicode 

def main : IO Unit := do
  let map := unicodeDataMap.get
  map.forM λ k v => IO.println s!"{k} -> {v}"
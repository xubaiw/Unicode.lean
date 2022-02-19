import Unicode

def main : IO Unit := do
  foo.forM λ k v => do
    IO.println s!"{k} -> {v}"

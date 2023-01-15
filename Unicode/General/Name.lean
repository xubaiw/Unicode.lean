import Unicode.Data

namespace Unicode

/-- Get unicode character name -/
@[inline]
def getName (c : Char) : Option String :=
  CharMap.find? Data.unicodeDataMap c |>.bind (·.get? 0)

end Unicode

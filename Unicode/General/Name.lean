import Unicode.Includes

namespace Unicode

def getName (c : Char) : Option String :=
  let map := unicodeDataMap.get
  map.find? c |>.bind (·.get? 0)
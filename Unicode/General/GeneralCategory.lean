import Unicode.Includes

namespace Unicode

/-- http://www.unicode.org/reports/tr44/#GC_Values_Table -/
inductive GeneralCategory where
  | uppercaseLetter
  | lowercaseLetter
  | titlecaseLetter
  | casedLetter
  | modifierLetter
  | otherLetter
  | letter
  | nonspacingMark
  | spacingMark
  | enclosingMark
  | mark
  | decimalNumber
  | letterNumber
  | otherNumber
  | number
  | connectorPunctuation
  | dashPunctuation
  | openPunctuation
  | closePunctuation
  | initialPunctuation
  | finalPunctuation
  | otherPunctuation
  | punctuation
  | mathSymbol
  | currencySymbol
  | modifierSymbol
  | otherSymbol
  | symbol
  | spaceSeparator
  | lineSeparator
  | paragraphSeparator
  | separator
  | control
  | format
  | surrogate
  | privateUse
  | unassigned
  | other
  deriving DecidableEq, Inhabited, Repr

namespace GeneralCategory

/-- Convert abbrevation `String` to `GeneralCategory`. -/
def fromString : String → GeneralCategory
  | "Lu" => uppercaseLetter
  | "Ll" => lowercaseLetter
  | "Lt" => titlecaseLetter
  | "LC" => casedLetter
  | "Lm" => modifierLetter
  | "Lo" => otherLetter
  | "L"  => letter
  | "Mn" => nonspacingMark
  | "Mc" => spacingMark
  | "Me" => enclosingMark
  | "M"  => mark
  | "Nd" => decimalNumber
  | "Nl" => letterNumber
  | "No" => otherNumber
  | "N"  => number
  | "Pc" => connectorPunctuation
  | "Pd" => dashPunctuation
  | "Ps" => openPunctuation
  | "Pe" => closePunctuation
  | "Pi" => initialPunctuation
  | "Pf" => finalPunctuation
  | "Po" => otherPunctuation
  | "P"  => punctuation
  | "Sm" => mathSymbol
  | "Sc" => currencySymbol
  | "Sk" => modifierSymbol
  | "So" => otherSymbol
  | "S"  => symbol
  | "Zs" => spaceSeparator
  | "Zl" => lineSeparator
  | "Zp" => paragraphSeparator
  | "Z"  => separator
  | "Cc" => control
  | "Cf" => format
  | "Cs" => surrogate
  | "Co" => privateUse
  | "Cn" => unassigned
  | "C"  => other
  | _ => unreachable!

/-- Convert `GeneralCategory` to abbrevation `String`. -/
def toString : GeneralCategory → String
  | uppercaseLetter       => "Lu"
  | lowercaseLetter       => "Ll"
  | titlecaseLetter       => "Lt"
  | casedLetter           => "LC"
  | modifierLetter        => "Lm"
  | otherLetter           => "Lo"
  | letter                => "L" 
  | nonspacingMark        => "Mn"
  | spacingMark           => "Mc"
  | enclosingMark         => "Me"
  | mark                  => "M" 
  | decimalNumber         => "Nd"
  | letterNumber          => "Nl"
  | otherNumber           => "No"
  | number                => "N" 
  | connectorPunctuation  => "Pc"
  | dashPunctuation       => "Pd"
  | openPunctuation       => "Ps"
  | closePunctuation      => "Pe"
  | initialPunctuation    => "Pi"
  | finalPunctuation      => "Pf"
  | otherPunctuation      => "Po"
  | punctuation           => "P" 
  | mathSymbol            => "Sm"
  | currencySymbol        => "Sc"
  | modifierSymbol        => "Sk"
  | otherSymbol           => "So"
  | symbol                => "S" 
  | spaceSeparator        => "Zs"
  | lineSeparator         => "Zl"
  | paragraphSeparator    => "Zp"
  | separator             => "Z" 
  | control               => "Cc"
  | format                => "Cf"
  | surrogate             => "Cs"
  | privateUse            => "Co"
  | unassigned            => "Cn"
  | other                 => "C" 

/-- Convert `GeneralCategory` to abbrevation `String`. -/
instance : ToString GeneralCategory := ⟨ GeneralCategory.toString ⟩ 

end GeneralCategory

/--
  Get `GeneralCategory` of a `Char`.

  *NOTE:* Grouping categories like `letter`, `mark`, `number`, `punctuation`, `symbol`, `separator`
  and `other` are not in return value. If you want to check if a `Char` is in these `GeneralCategory`,
  use `charInGeneralCategory` instead.
-/
def getGeneralCategory (c : Char) : GeneralCategory :=
  let map := unicodeDataMap.get
  match map.find? c with
  | some list => GeneralCategory.fromString $ list.get! 1
  | none => GeneralCategory.unassigned

open GeneralCategory in
/-- Check if a `Char` is in given `GeneralCategory`. -/
def charInGeneralCategory (c : Char) (gc: GeneralCategory) : Bool :=
  let cat := getGeneralCategory c
  if gc = cat then
    true
  else
    match gc with
    | letter => cat = casedLetter || cat = modifierLetter || cat = otherLetter
    | mark => cat = nonspacingMark || cat = spacingMark || cat = enclosingMark
    | number => cat = decimalNumber || cat = letterNumber || cat = otherNumber
    | punctuation => cat = connectorPunctuation || cat = dashPunctuation || cat = openPunctuation || cat = closePunctuation || cat = initialPunctuation || cat = finalPunctuation || cat = otherPunctuation
    | symbol => cat = mathSymbol || cat = currencySymbol || cat = modifierSymbol || cat = otherSymbol
    | separator => cat = spaceSeparator || cat = lineSeparator || cat = paragraphSeparator
    | other => cat = GeneralCategory.control || cat = format || cat = surrogate || cat = privateUse || cat = unassigned
    | _ => false

end Unicode
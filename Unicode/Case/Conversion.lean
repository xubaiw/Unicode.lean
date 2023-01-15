import Unicode.Data

namespace Unicode

/-- Case folding

  Case folding is used to compare characters in a case-insensitive manner. For example, `foldCase 'A' = foldCase 'a'`.

  Note that the result may have length greater than 1. For example, `foldCase 'ß' = "ss"`. See also `simpleCaseFolding`.
-/
def foldCase (c : Char) : String :=
  match CharMap.find? Data.fullCaseFoldMap c with
  | some v => v
  | none => toString c

/-- Lowercase conversion

  Converts a letter to its lowercase counterpart. For example, `toLower 'A' = "a"`.

  Note that the result may have length greater than 1. For example, `toLower 'ß' = "ss"`. See also `toSimpleLower`.
-/
def toLower (c : Char) : String :=
  match CharMap.find? Data.fullLowercaseMap c with
  | some v => v
  | none => toString c

/-- Uppercase conversion

  Converts a letter to its uppercase counterpart. For example, `toUpper 'a' = "A"`.

  Note that the result may have length greater than 1. For example, `toUpper 'ß' = "SS"`. See also `toSimpleUpper`.
-/
def toUpper (c : Char) : String :=
  match CharMap.find? Data.fullUppercaseMap c with
  | some v => v
  | none => toString c

/-- Titlecase conversion

  Converts a letter to its titlecase counterpart. For example, `toTitle 'a' = 'A'`.

  Note that the result may have length greater than 1. For example, `toTitle 'ß' = "Ss"`. See also `toSimpleTitle`.
-/
def toTitle (c : Char) : String :=
  match CharMap.find? Data.fullTitlecaseMap c with
  | some v => v
  | none => toString c

/-- Simple case folding

  Case folding is used to compare characters in a case-insensitive manner. For example, `simpleFoldCase 'A' = simpleFoldCase 'a'`.

  Note that case folding does not always map to lowercase. For example, Cherokee letters generally fold to their uppercase form.

  This does not handle the cases where the appropriate folding would have more than one character; see `foldCase`. -/
def foldCaseSimple (c : Char) : Char :=
  match CharMap.find? Data.simpleCaseFoldMap c with
  | some v => v
  | none => c

/-- Simple lowercase conversion

  Converts a letter to its lowercase counterpart. For example, `toSimpleLower 'A' = 'a'`.

  This does not handle the cases where the appropriate lowercase counterpart would have more than one character; see `toLower`. -/
def toLowerSimple (c : Char) : Char :=
  match CharMap.find? Data.simpleLowercaseMap c with
  | some v => v
  | none => c

/-- Simple uppercase conversion

  Converts a letter to its uppercase counterpart. For example, `toSimpleUpper 'a' = 'A'`.

  This does not handle the cases where the appropriate uppercase counterpart would have more than one character; see `toUpper`. -/
def toUpperSimple (c : Char) : Char :=
  match CharMap.find? Data.simpleUppercaseMap c with
  | some v => v
  | none => c

/-- Simple titlecase conversion

  Converts a letter to its titlecase counterpart. For example, `toSimpleTitle 'a' = 'A'`.

  This does not handle the cases where the appropriate titlecase counterpart would have more than one character; see `toTitlecase`. -/
def toTitleSimple (c : Char) : Char :=
  match CharMap.find? Data.simpleTitlecaseMap c with
  | some v => v
  | none => c

end Unicode


import Std.Data.HashMap
import Std.Data.RBMap
import Unicode.Data.Includes

/-- Decode a string of hex digits into a number, the string may include a `0x` prefix -/
protected def Nat.ofHexString? (str : String) : Option Nat :=
  let str := if "0x".isPrefixOf str then str.drop 2 else str
  str.foldl fn (some 0)
where
  fn : Option Nat → Char → Option Nat
  | some n, '0' => some <| 16 * n
  | some n, '1' => some <| 16 * n + 1
  | some n, '2' => some <| 16 * n + 2
  | some n, '3' => some <| 16 * n + 3
  | some n, '4' => some <| 16 * n + 4
  | some n, '5' => some <| 16 * n + 5
  | some n, '6' => some <| 16 * n + 6
  | some n, '7' => some <| 16 * n + 7
  | some n, '8' => some <| 16 * n + 8
  | some n, '9' => some <| 16 * n + 9
  | some n, 'A' | some n, 'a' => some <| 16 * n + 10
  | some n, 'B' | some n, 'b' => some <| 16 * n + 11
  | some n, 'C' | some n, 'c' => some <| 16 * n + 12
  | some n, 'D' | some n, 'd' => some <| 16 * n + 13
  | some n, 'E' | some n, 'e' => some <| 16 * n + 14
  | some n, 'F' | some n, 'f' => some <| 16 * n + 15
  | _, _ => none

@[inline, inherit_doc Nat.ofHexString?]
protected def Nat.ofHexString! (str : String) : Nat :=
  match Nat.ofHexString? str with
  | some n => n
  | none => panic! s!"invalid hex string {repr str}"

/-- Decode a string of hex digits into a character, the string may include a `U+` prefix -/
@[inline]
protected def Char.ofHexString? (str : String) : Option Char :=
  let str := if "U+".isPrefixOf str then str.drop 2 else str
  Nat.ofHexString? str |>.map Char.ofNat

@[inline, inherit_doc Char.ofHexString?]
protected def Char.ofHexString! (str : String) : Char :=
  match Char.ofHexString? str with
  | some c => c
  | none => panic! s!"invalid character hex string {repr str}"

private partial def String.splitOn'Aux (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : Array String) : Array String :=
  if s.atEnd i then
    if sep.atEnd j then
      r.push (s.extract b (i - j)) |>.push ""
    else
      r.push (s.extract b i)
  else if s.get i == sep.get j then
    let i := s.next i
    let j := sep.next j
    if sep.atEnd j then
      splitOn'Aux s sep i i 0 <| r.push (s.extract b (i - j))
    else
      splitOn'Aux s sep b i j r
  else
    splitOn'Aux s sep b (s.next i) 0 r

/-- Like `String.splitOn` but returns an array instead of a list -/
def String.splitOn' (s : String) (sep : String := " ") : Array String :=
  if sep == "" then #[s] else splitOn'Aux s sep 0 0 0 #[]

namespace Unicode

-- Make `Char` `Hashable` as key of `HashMap`
instance : Hashable Char := ⟨fun c => hash c.val⟩

-- Make `Char` `Ord` as a key of `RBMap`
instance : Ord Char := ⟨fun a b => compare a.val b.val⟩

/-- Abstraction class for mappings from `Char` -/
class CharMap (τ : Type _) (α : outParam (Type _)) where
  find? : τ → Char → Option α

@[inline, always_inline]
instance (α) : CharMap (Std.AssocList Char α) α where
  find? m := m.find?

@[inline, always_inline]
instance (α) : CharMap (Std.HashMap Char α) α where
  find? m := m.find?

@[inline, always_inline]
instance (α) : CharMap (Std.RBMap Char α compare) α where
  find? m := m.find?

@[inline, always_inline]
instance (τ α) [CharMap τ α] : CharMap (Thunk τ) α where
  find? m := CharMap.find? m.get

namespace Data

/-- Split string into lines, discarding `#`-prefixed comments, trailing spaces, and dropping empty lines -/
def splitLines (str : String) : Array String := Id.run do
  let mut arr := #[]
  for line in str.splitOn "\n" do
    let line := (line.takeWhile (·!='#')).trimRight
    if !line.isEmpty then
      arr := arr.push line
  return arr

/-- Parse data file `String` into `HashMap` -/
def parseStrToMapFn (s : String) : Std.HashMap Char (List String) := Id.run do
  let mut rangeStarts := Std.HashMap.empty
  let mut result := Std.HashMap.empty
  for line in splitLines s do
    let splits := line.splitOn ";" |>.map (·.splitOn "\t") |>.join |>.map String.trim
    let first := splits.head! |>.replace "U+" ""
    -- range
    if first.contains '.' then
      let splits := first.splitOn ".."
      let start := Nat.ofHexString! splits.head!
      let stop := Nat.ofHexString! splits.getLast!
      for val in [start:(stop+1)] do
        result := result.insert (.ofNat val) (splits.tail!)
    -- mutiple
    else if first.contains ' ' then
      let splits := first.splitOn " "
      for val in splits do
        result := result.insert (.ofNat <| Nat.ofHexString! val) (splits.tail!)
    else
      if let some second := splits.get? 1 then
        -- backward range start
        if second.endsWith ", First>" then
          let name := second |>.replace ", First>" "" |>.replace "<" ""
          rangeStarts := rangeStarts.insert name (Nat.ofHexString! first)
        -- backward range end
        else if second.endsWith ", Last>" then
          let name := second |>.replace ", Last>" "" |>.replace "<" ""
          let start := rangeStarts.find! name
          let stop := Nat.ofHexString! first
          let newTail := name::splits.tail!.tail!
          for val in [start:(stop+1)] do
            result := result.insert (.ofNat val) newTail
        -- single
        else
          result := result.insert (.ofNat <| Nat.ofHexString! first) (splits.tail!)
      -- single
      else
        result := result.insert (.ofNat <| Nat.ofHexString! first) (splits.tail!)
  return result

/-- Map from UnicodeData.txt -/
def unicodeDataMap : Thunk <| Std.HashMap Char (List String) := Id.run do
  let mut m := Std.HashMap.empty
  for line in splitLines unicodeDataStr do
    match line.splitOn ";" with
    | chr :: lst => m := m.insert (Char.ofHexString! chr) (lst.take 14)
    | _ => panic! "invalid data from UnicodeData.txt"
  return m

/-- Simple lowercase map from UnicodeData.txt -/
def simpleLowercaseMap : Thunk <| Std.HashMap Char Char :=
  unicodeDataMap.get.filterMap fun _ lst =>
    if (lst.get! 11).isEmpty then none else
      some (Char.ofHexString! (lst.get! 11))

/-- Simple uppercase map from UnicodeData.txt -/
def simpleUppercaseMap : Thunk <| Std.HashMap Char Char :=
  unicodeDataMap.get.filterMap fun _ lst =>
    if (lst.get! 13).isEmpty then none else
      some (Char.ofHexString! (lst.get! 13))

/-- Simple titlecase map from UnicodeData.txt -/
-- small so no need to thunk
def simpleTitlecaseMap : Std.HashMap Char Char :=
  unicodeDataMap.get.filterMap fun chr lst =>
    if (lst.get! 12).isEmpty then
      -- default to uppercase
      CharMap.find? simpleUppercaseMap chr
    else
      some (Char.ofHexString! (lst.get! 12))

/-- Simple case folding map from CaseFolding.txt -/
def simpleCaseFoldMap : Thunk <| Std.HashMap Char Char := Id.run do
  let mut m := Std.HashMap.empty
  for line in splitLines caseFoldingStr do
    match (line.push ' ').splitOn "; " with
    | chr :: cat :: val :: _ =>
      -- only common and simple mappings
      if cat == "C" || cat == "S" then
        m := m.insert (Char.ofHexString! chr) (Char.ofHexString! val)
    | _ => panic! "invalid data from CaseFolding.txt"
  return m

/-- Full lowercase map from UnicodeData.txt and SpecialCasing.txt -/
def fullLowercaseMap : Thunk <| Std.HashMap Char String := Id.run do
  let mut m := simpleLowercaseMap.get.mapVal fun _ v => v.toString
  for line in splitLines specialCasingStr do
    match (line.push ' ').splitOn "; " with
    | chr :: lst =>
      -- skip conditional mappings
      if (lst.get! 3).isEmpty then
        let val := (lst.get! 0).splitOn.map Char.ofHexString!
        m := m.insert (Char.ofHexString! chr) (String.mk val)
    | _ => panic! "invalid data from SpecialCasing.txt"
  return m

/-- Full lowercase map from UnicodeData.txt and SpecialCasing.txt -/
def fullUppercaseMap : Thunk <| Std.HashMap Char String := Id.run do
  let mut m := simpleUppercaseMap.get.mapVal fun _ v => v.toString
  for line in splitLines specialCasingStr do
    match (line.push ' ').splitOn "; " with
    | chr :: lst =>
      -- skip conditional mappings
      if (lst.get! 3).isEmpty then
        let val := (lst.get! 2).splitOn.map Char.ofHexString!
        m := m.insert (Char.ofHexString! chr) (String.mk val)
    | _ => panic! "invalid data from SpecialCasing.txt"
  return m

/-- Full titlecase map from UnicodeData.txt and SpecialCasing.txt -/
def fullTitlecaseMap : Thunk <| Std.HashMap Char String := Id.run do
  let mut m := simpleUppercaseMap.get.mapVal fun _ v => v.toString
  for line in splitLines specialCasingStr do
    match (line.push ' ').splitOn "; " with
    | chr :: lst =>
      -- skip conditional mappings
      if (lst.get! 3).isEmpty then
        let val := (lst.get! 1).splitOn.map Char.ofHexString!
        m := m.insert (Char.ofHexString! chr) (String.mk val)
    | _ => panic! "invalid data from SpecialCasing.txt"
  return m

/-- Full case folding map from CaseFolding.txt -/
def fullCaseFoldMap : Thunk <| Std.HashMap Char String := Id.run do
  let mut m := Std.HashMap.empty
  for line in splitLines caseFoldingStr do
    match (line.push ' ').splitOn "; " with
    | chr :: cat :: val :: _ =>
      -- only common and full mappings
      if cat == "C" || cat == "F" then
        let val := val.splitOn.map Char.ofHexString!
        m := m.insert (Char.ofHexString! chr) (String.mk val)
    | _ => panic! "invalid data from CaseFolding.txt"
  return m

section Thunks

/-!
  ### UCD Main Directory
-/

/-- Includes the ArabicShaping.txt data. -/
def arabicShapingMap := Thunk.mk fun _ => parseStrToMapFn arabicShapingStr

/-- Includes the BidiBrackets.txt data. -/
def bidiBracketsMap := Thunk.mk fun _ => parseStrToMapFn bidiBracketsStr

/-- Includes the BidiMirroring.txt data. -/
def bidiMirroringMap := Thunk.mk fun _ => parseStrToMapFn bidiMirroringStr

/-- Includes the NormalizationCorrections.txt data. -/
def normalizationCorrectionsMap := Thunk.mk fun _ => parseStrToMapFn normalizationCorrectionsStr

/-- Includes the Blocks.txt data. -/
def blocksMap := Thunk.mk fun _ => parseStrToMapFn blocksStr

/-- Includes the NushuSources.txt data. -/
def nushuSourcesMap := Thunk.mk fun _ => parseStrToMapFn nushuSourcesStr

/-- Includes the PropList.txt data. -/
def propListMap := Thunk.mk fun _ => parseStrToMapFn propListStr

/-- Includes the CompositionExclusions.txt data. -/
def compositionExclusionsMap := Thunk.mk fun _ => parseStrToMapFn compositionExclusionsStr

/-- Includes the DerivedAge.txt data. -/
def derivedAgeMap := Thunk.mk fun _ => parseStrToMapFn derivedAgeStr

/-- Includes the ScriptExtensions.txt data. -/
def scriptExtensionsMap := Thunk.mk fun _ => parseStrToMapFn scriptExtensionsStr

/-- Includes the DerivedCoreProperties.txt data. -/
def derivedCorePropertiesMap := Thunk.mk fun _ => parseStrToMapFn derivedCorePropertiesStr

/-- Includes the Scripts.txt data. -/
def scriptsMap := Thunk.mk fun _ => parseStrToMapFn scriptsStr

/-- Includes the DerivedNormalizationProps.txt data. -/
def derivedNormalizationPropsMap := Thunk.mk fun _ => parseStrToMapFn derivedNormalizationPropsStr

/-- Includes the EastAsianWidth.txt data. -/
def eastAsianWidthMap := Thunk.mk fun _ => parseStrToMapFn eastAsianWidthStr

/-- Includes the EquivalentUnifiedIdeograph.txt data. -/
def equivalentUnifiedIdeographMap := Thunk.mk fun _ => parseStrToMapFn equivalentUnifiedIdeographStr

/-- Includes the HangulSyllableType.txt data. -/
def hangulSyllableTypeMap := Thunk.mk fun _ => parseStrToMapFn hangulSyllableTypeStr

/-- Includes the IndicPositionalCategory.txt data. -/
def indicPositionalCategoryMap := Thunk.mk fun _ => parseStrToMapFn indicPositionalCategoryStr

/-- Includes the VerticalOrientation.txt data. -/
def verticalOrientationMap := Thunk.mk fun _ => parseStrToMapFn verticalOrientationStr

/-- Includes the IndicSyllabicCategory.txt data. -/
def indicSyllabicCategoryMap := Thunk.mk fun _ => parseStrToMapFn indicSyllabicCategoryStr

/-- Includes the Jamo.txt data. -/
def jamoMap := Thunk.mk fun _ => parseStrToMapFn jamoStr

/-- Includes the LineBreak.txt data. -/
def lineBreakMap := Thunk.mk fun _ => parseStrToMapFn lineBreakStr

/-- Includes the NameAliases.txt data. -/
def nameAliasesMap := Thunk.mk fun _ => parseStrToMapFn nameAliasesStr

/-!
  ### Auxiliary Subdirectory
-/

/-- Includes the GraphemeBreakProperty.txt data. -/
def graphemeBreakPropertyMap := Thunk.mk fun _ => parseStrToMapFn graphemeBreakPropertyStr

/-- Includes the WordBreakProperty.txt data. -/
def wordBreakPropertyMap := Thunk.mk fun _ => parseStrToMapFn wordBreakPropertyStr

/-- Includes the SentenceBreakProperty.txt data. -/
def sentenceBreakPropertyMap := Thunk.mk fun _ => parseStrToMapFn sentenceBreakPropertyStr

/-!
  ### Emoji Subdirectory
-/

/-- Includes the emoji-data.txt data. -/
def emojiDataMap := Thunk.mk fun _ => parseStrToMapFn emojiDataStr

/-!
  ### Extracted Subdirectory
-/

/-- Includes the DerivedBidiClass.txt string. -/
def derivedBidiClassMap := Thunk.mk fun _ => parseStrToMapFn derivedBidiClassStr

/-- Includes the DerivedJoiningGroup.txt string. -/
def derivedJoiningGroupMap := Thunk.mk fun _ => parseStrToMapFn derivedJoiningGroupStr

/-- Includes the DerivedBinaryProperties.txt string. -/
def derivedBinaryPropertiesMap := Thunk.mk fun _ => parseStrToMapFn derivedBinaryPropertiesStr

/-- Includes the DerivedJoiningType.txt string. -/
def derivedJoiningTypeMap := Thunk.mk fun _ => parseStrToMapFn derivedJoiningTypeStr

/-- Includes the DerivedCombiningClass.txt string. -/
def derivedCombiningClassMap := Thunk.mk fun _ => parseStrToMapFn derivedCombiningClassStr

/-- Includes the DerivedLineBreak.txt string. -/
def derivedLineBreakMap := Thunk.mk fun _ => parseStrToMapFn derivedLineBreakStr

/-- Includes the DerivedDecompositionType.txt string. -/
def derivedDecompositionTypeMap := Thunk.mk fun _ => parseStrToMapFn derivedDecompositionTypeStr

/-- Includes the DerivedName.txt string. -/
def derivedNameMap := Thunk.mk fun _ => parseStrToMapFn derivedNameStr

/-- Includes the DerivedEastAsianWidth.txt string. -/
def derivedEastAsianWidthMap := Thunk.mk fun _ => parseStrToMapFn derivedEastAsianWidthStr

/-- Includes the DerivedNumericType.txt string. -/
def derivedNumericTypeMap := Thunk.mk fun _ => parseStrToMapFn derivedNumericTypeStr

/-- Includes the DerivedGeneralCategory.txt string. -/
def derivedGeneralCategoryMap := Thunk.mk fun _ => parseStrToMapFn derivedGeneralCategoryStr

/-- Includes the DerivedNumericValues.txt string. -/
def derivedNumericValuesMap := Thunk.mk fun _ => parseStrToMapFn derivedNumericValuesStr

/-!
  ### Unihan Subdirectory
-/

/-- Includes the Unihan_DictionaryIndices.txt string. -/
def unihanDictionaryIndicesMap := Thunk.mk fun _ => parseStrToMapFn unihanDictionaryIndicesStr

/-- Includes the Unihan_OtherMappings.txt string. -/
def unihanOtherMappingsMap := Thunk.mk fun _ => parseStrToMapFn unihanOtherMappingsStr

/-- Includes the Unihan_DictionaryLikeData.txt string. -/
def unihanDictionaryLikeDataMap := Thunk.mk fun _ => parseStrToMapFn unihanDictionaryLikeDataStr

/-- Includes the Unihan_RadicalStrokeCounts.txt string. -/
def unihanRadicalStrokeCountsMap := Thunk.mk fun _ => parseStrToMapFn unihanRadicalStrokeCountsStr

/-- Includes the Unihan_IRGSources.txt string. -/
def unihanIRGSourcesMap := Thunk.mk fun _ => parseStrToMapFn unihanIRGSourcesStr

/-- Includes the Unihan_Readings.txt string. -/
def unihanReadingsMap := Thunk.mk fun _ => parseStrToMapFn unihanReadingsStr

/-- Includes the Unihan_NumericValues.txt string. -/
def unihanNumericValuesMap := Thunk.mk fun _ => parseStrToMapFn unihanNumericValuesStr

/-- Includes the Unihan_Variants.txt string. -/
def unihanVariantsMap := Thunk.mk fun _ => parseStrToMapFn unihanVariantsStr

end Thunks

end Unicode.Data

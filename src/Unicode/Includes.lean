-- import Mathlib.Util.IncludeStr
import Std.Data.HashMap
import Lean

open Std System
 
partial def String.splitOn'Aux (s sep : String) (b : Pos) (i : Pos) (j : Pos) (r : Array String) : Array String :=
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

def String.splitOn' (s : String) (sep : String := " ") : Array String :=
  if sep == "" then #[s] else splitOn'Aux s sep 0 0 0 #[]

def Option.flatten : (o : Option (Option A)) → Option A
  | some opt => opt
  | none => none

def System.FilePath.parentN (fp : FilePath) : Nat → Option FilePath
  | 0 => fp.parent
  | Nat.succ n => (fp.parentN n).map FilePath.parent |> Option.flatten

namespace Mathlib.Util

elab (name := includeStr) "include_ucd_str " str:str : term => do
  let some str := str.isStrLit? | Lean.Elab.throwUnsupportedSyntax
  let srcDir := System.FilePath.mk ((← IO.getEnv "UCD_DIR").getD "./UCD")
  let path := srcDir / str
  Lean.mkStrLit <$> IO.FS.readFile path

end Mathlib.Util

namespace Unicode

/-!
  ## Included Raw Strings

  ### UCD Main Directory
-/

/-- Includes the ArabicShaping.txt string. -/
def arabicShapingStr := include_ucd_str "ArabicShaping.txt"

/-- Includes the BidiBrackets.txt string. -/
def bidiBracketsStr := include_ucd_str "BidiBrackets.txt"

/-- Includes the BidiMirroring.txt string. -/
def bidiMirroringStr := include_ucd_str "BidiMirroring.txt"

/-- Includes the NormalizationCorrections.txt string. -/
def normalizationCorrectionsStr := include_ucd_str "NormalizationCorrections.txt"

/-- Includes the Blocks.txt string. -/
def blocksStr := include_ucd_str "Blocks.txt"

/-- Includes the NushuSources.txt string. -/
def nushuSourcesStr := include_ucd_str "NushuSources.txt"

/-- Includes the PropList.txt string. -/
def propListStr := include_ucd_str "PropList.txt"

/-- Includes the CaseFolding.txt string. -/
def caseFoldingStr := include_ucd_str "CaseFolding.txt"

/-- Includes the CompositionExclusions.txt string. -/
def compositionExclusionsStr := include_ucd_str "CompositionExclusions.txt"
  
/-- Includes the DerivedAge.txt string. -/
def derivedAgeStr := include_ucd_str "DerivedAge.txt"

/-- Includes the ScriptExtensions.txt string. -/
def scriptExtensionsStr := include_ucd_str "ScriptExtensions.txt"

/-- Includes the DerivedCoreProperties.txt string. -/
def derivedCorePropertiesStr := include_ucd_str "DerivedCoreProperties.txt"

/-- Includes the Scripts.txt string. -/
def scriptsStr := include_ucd_str "Scripts.txt"

/-- Includes the DerivedNormalizationProps.txt string. -/
def derivedNormalizationPropsStr := include_ucd_str "DerivedNormalizationProps.txt"

/-- Includes the SpecialCasing.txt string. -/
def specialCasingStr := include_ucd_str "SpecialCasing.txt"

/-- Includes the EastAsianWidth.txt string. -/
def eastAsianWidthStr := include_ucd_str "EastAsianWidth.txt"

/-- Includes the EquivalentUnifiedIdeograph.txt string. -/
def equivalentUnifiedIdeographStr := include_ucd_str "EquivalentUnifiedIdeograph.txt"

/-- Includes the HangulSyllableType.txt string. -/
def hangulSyllableTypeStr := include_ucd_str "HangulSyllableType.txt"

/-- Includes the UnicodeData.txt string. See `unicodeDataMap`. -/
def unicodeDataStr := include_ucd_str "UnicodeData.txt"

/-- Includes the IndicPositionalCategory.txt string. -/
def indicPositionalCategoryStr := include_ucd_str "IndicPositionalCategory.txt"

/-- Includes the VerticalOrientation.txt string. -/
def verticalOrientationStr := include_ucd_str "VerticalOrientation.txt"

/-- Includes the IndicSyllabicCategory.txt string. -/
def indicSyllabicCategoryStr := include_ucd_str "IndicSyllabicCategory.txt"

/-- Includes the Jamo.txt string. -/
def jamoStr := include_ucd_str "Jamo.txt"

/-- Includes the LineBreak.txt string. -/
def lineBreakStr := include_ucd_str "LineBreak.txt"

/-- Includes the NameAliases.txt string. -/
def nameAliasesStr := include_ucd_str "NameAliases.txt"

/-!
  ### Auxiliary Subdirectory
-/

/-- Includes the GraphemeBreakProperty.txt string. -/
def graphemeBreakPropertyStr := include_ucd_str "auxiliary/GraphemeBreakProperty.txt"

/-- Includes the WordBreakProperty.txt string. -/
def wordBreakPropertyStr := include_ucd_str "auxiliary/WordBreakProperty.txt"
  
/-- Includes the SentenceBreakProperty.txt string. -/
def sentenceBreakPropertyStr := include_ucd_str "auxiliary/SentenceBreakProperty.txt"

/-!
  ### Emoji Subdirectory
-/

/-- Includes the emoji-data.txt string. -/
def emojiDataStr := include_ucd_str "emoji/emoji-data.txt"

/-!
  ### Extracted Subdirectory
-/

/-- Includes the DerivedBidiClass.txt string. -/
def derivedBidiClassStr := include_ucd_str "extracted/DerivedBidiClass.txt"

/-- Includes the DerivedJoiningGroup.txt string. -/
def derivedJoiningGroupStr := include_ucd_str "extracted/DerivedJoiningGroup.txt"

/-- Includes the DerivedBinaryProperties.txt string. -/
def derivedBinaryPropertiesStr := include_ucd_str "extracted/DerivedBinaryProperties.txt"

/-- Includes the DerivedJoiningType.txt string. -/
def derivedJoiningTypeStr := include_ucd_str "extracted/DerivedJoiningType.txt"

/-- Includes the DerivedCombiningClass.txt string. -/
def derivedCombiningClassStr := include_ucd_str "extracted/DerivedCombiningClass.txt"

/-- Includes the DerivedLineBreak.txt string. -/
def derivedLineBreakStr := include_ucd_str "extracted/DerivedLineBreak.txt"

/-- Includes the DerivedDecompositionType.txt string. -/
def derivedDecompositionTypeStr := include_ucd_str "extracted/DerivedDecompositionType.txt"

/-- Includes the DerivedName.txt string. -/
def derivedNameStr := include_ucd_str "extracted/DerivedName.txt"

/-- Includes the DerivedEastAsianWidth.txt string. -/
def derivedEastAsianWidthStr := include_ucd_str "extracted/DerivedEastAsianWidth.txt"

/-- Includes the DerivedNumericType.txt string. -/
def derivedNumericTypeStr := include_ucd_str "extracted/DerivedNumericType.txt"

/-- Includes the DerivedGeneralCategory.txt string. -/
def derivedGeneralCategoryStr := include_ucd_str "extracted/DerivedGeneralCategory.txt"

/-- Includes the DerivedNumericValues.txt string. -/
def derivedNumericValuesStr := include_ucd_str "extracted/DerivedNumericValues.txt"

/-!
  ### Unihan Subdirectory
-/

/-- Includes the Unihan_DictionaryIndices.txt string. -/
def unihanDictionaryIndicesStr := include_ucd_str "Unihan/Unihan_DictionaryIndices.txt"

/-- Includes the Unihan_OtherMappings.txt string. -/
def unihanOtherMappingsStr := include_ucd_str "Unihan/Unihan_OtherMappings.txt"

/-- Includes the Unihan_DictionaryLikeData.txt string. -/
def unihanDictionaryLikeDataStr := include_ucd_str "Unihan/Unihan_DictionaryLikeData.txt"

/-- Includes the Unihan_RadicalStrokeCounts.txt string. -/
def unihanRadicalStrokeCountsStr := include_ucd_str "Unihan/Unihan_RadicalStrokeCounts.txt"

/-- Includes the Unihan_IRGSources.txt string. -/
def unihanIRGSourcesStr := include_ucd_str "Unihan/Unihan_IRGSources.txt"

/-- Includes the Unihan_Readings.txt string. -/
def unihanReadingsStr := include_ucd_str "Unihan/Unihan_Readings.txt"

/-- Includes the Unihan_NumericValues.txt string. -/
def unihanNumericValuesStr := include_ucd_str "Unihan/Unihan_NumericValues.txt"

/-- Includes the Unihan_Variants.txt string. -/
def unihanVariantsStr := include_ucd_str "Unihan/Unihan_Variants.txt"

/-!
  ## HashMap Thunks
-/

/-- Decode hex string into number. -/
private def decodeHex! (s : String) : Nat :=
  s.data.map char2Nat
  |>.foldl foldlHexDigits 0
  where
    char2Nat c := match c with
    | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
    | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
    | 'a' => 10 | 'b' => 11 | 'c' => 12 | 'd' => 13 | 'e' => 14 | 'f' => 15
    | 'A' => 10 | 'B' => 11 | 'C' => 12 | 'D' => 13 | 'E' => 14 | 'F' => 15
    | c => panic! s!"Invalid hex digit {c}"
    foldlHexDigits acc d := 16 * acc + d

/-- Make `Char` `Hashable` as key of `HashMap`. -/
instance : Hashable Char := ⟨ λ c => String.hash $ toString c ⟩ 

/-- Parse data file `String` into `HashMap`, the unit in parameter is left for `Thunk`. -/
def parseStrToMapFn (s : String) (unit : Unit) : HashMap Char (List String)  := Id.run do
  let mut rangeStarts := HashMap.empty
  let mut result := .empty
  for line in s.splitOn' "\n" |>.filterMap lineCleanup do
    let splits := line.splitOn ";" |>.map (·.splitOn "\t") |>.join |>.map String.trim
    let first := splits.head! |>.replace "U+" ""
    -- range
    if first.contains '.' then
      let splits := first.splitOn ".."
      let start := decodeHex! splits.head!
      let stop := decodeHex! splits.getLast!
      for val in [start:(stop+1)] do
        result := result.insert (.ofNat val) (splits.tail!)
    -- mutiple
    else if first.contains ' ' then
      let splits := first.splitOn " "
      for val in splits do
        result := result.insert (.ofNat $ decodeHex! val) (splits.tail!)
    else
      if let some second := splits.get? 1 then
        -- backward range start
        if second.endsWith ", First>" then
          let name := second |>.replace ", First>" "" |>.replace "<" ""
          rangeStarts := rangeStarts.insert name (decodeHex! first)
        -- backward range end
        else if second.endsWith ", Last>" then
          let name := second |>.replace ", Last>" "" |>.replace "<" ""
          let start := rangeStarts.find! name
          let stop := decodeHex! first
          let newTail := name::splits.tail!.tail!
          for val in [start:(stop+1)] do
            result := result.insert (.ofNat val) newTail
        -- single
        else
          result := result.insert (.ofNat $ decodeHex! first) (splits.tail!)
      -- single
      else
        result := result.insert (.ofNat $ decodeHex! first) (splits.tail!)
  return result
where
  /-- Remove comments and empty lines. -/
  lineCleanup (line : String) : Option String :=
    line.splitOn "#"
    |>.head?
    |>.filter (·.trim ≠ "")

/-!
  ### UCD Main Directory
-/

/-- Includes the ArabicShaping.txt data. -/
def arabicShapingMap := Thunk.mk $ parseStrToMapFn arabicShapingStr

/-- Includes the BidiBrackets.txt data. -/
def bidiBracketsMap := Thunk.mk $ parseStrToMapFn bidiBracketsStr

/-- Includes the BidiMirroring.txt data. -/
def bidiMirroringMap := Thunk.mk $ parseStrToMapFn bidiMirroringStr

/-- Includes the NormalizationCorrections.txt data. -/
def normalizationCorrectionsMap := Thunk.mk $ parseStrToMapFn normalizationCorrectionsStr

/-- Includes the Blocks.txt data. -/
def blocksMap := Thunk.mk $ parseStrToMapFn blocksStr

/-- Includes the NushuSources.txt data. -/
def nushuSourcesMap := Thunk.mk $ parseStrToMapFn nushuSourcesStr

/-- Includes the PropList.txt data. -/
def propListMap := Thunk.mk $ parseStrToMapFn propListStr

/-- Includes the CaseFolding.txt data. -/
def caseFoldingMap := Thunk.mk $ parseStrToMapFn caseFoldingStr

/-- Includes the CompositionExclusions.txt data. -/
def compositionExclusionsMap := Thunk.mk $ parseStrToMapFn compositionExclusionsStr
  
/-- Includes the DerivedAge.txt data. -/
def derivedAgeMap := Thunk.mk $ parseStrToMapFn derivedAgeStr

/-- Includes the ScriptExtensions.txt data. -/
def scriptExtensionsMap := Thunk.mk $ parseStrToMapFn scriptExtensionsStr

/-- Includes the DerivedCoreProperties.txt data. -/
def derivedCorePropertiesMap := Thunk.mk $ parseStrToMapFn derivedCorePropertiesStr

/-- Includes the Scripts.txt data. -/
def scriptsMap := Thunk.mk $ parseStrToMapFn scriptsStr

/-- Includes the DerivedNormalizationProps.txt data. -/
def derivedNormalizationPropsMap := Thunk.mk $ parseStrToMapFn derivedNormalizationPropsStr

/-- Includes the SpecialCasing.txt data. -/
def specialCasingMap := Thunk.mk $ parseStrToMapFn specialCasingStr

/-- Includes the EastAsianWidth.txt data. -/
def eastAsianWidthMap := Thunk.mk $ parseStrToMapFn eastAsianWidthStr

/-- Includes the EquivalentUnifiedIdeograph.txt data. -/
def equivalentUnifiedIdeographMap := Thunk.mk $ parseStrToMapFn equivalentUnifiedIdeographStr

/-- Includes the HangulSyllableType.txt data. -/
def hangulSyllableTypeMap := Thunk.mk $ parseStrToMapFn hangulSyllableTypeStr

/-- Includes the UnicodeData.txt data. See `unicodeDataMap`. -/
def unicodeDataMap := Thunk.mk $ parseStrToMapFn unicodeDataStr

/-- Includes the IndicPositionalCategory.txt data. -/
def indicPositionalCategoryMap := Thunk.mk $ parseStrToMapFn indicPositionalCategoryStr

/-- Includes the VerticalOrientation.txt data. -/
def verticalOrientationMap := Thunk.mk $ parseStrToMapFn verticalOrientationStr

/-- Includes the IndicSyllabicCategory.txt data. -/
def indicSyllabicCategoryMap := Thunk.mk $ parseStrToMapFn indicSyllabicCategoryStr

/-- Includes the Jamo.txt data. -/
def jamoMap := Thunk.mk $ parseStrToMapFn jamoStr

/-- Includes the LineBreak.txt data. -/
def lineBreakMap := Thunk.mk $ parseStrToMapFn lineBreakStr

/-- Includes the NameAliases.txt data. -/
def nameAliasesMap := Thunk.mk $ parseStrToMapFn nameAliasesStr

/-!
  ### Auxiliary Subdirectory
-/

/-- Includes the GraphemeBreakProperty.txt data. -/
def graphemeBreakPropertyMap := Thunk.mk $ parseStrToMapFn graphemeBreakPropertyStr

/-- Includes the WordBreakProperty.txt data. -/
def wordBreakPropertyMap := Thunk.mk $ parseStrToMapFn wordBreakPropertyStr
  
/-- Includes the SentenceBreakProperty.txt data. -/
def sentenceBreakPropertyMap := Thunk.mk $ parseStrToMapFn sentenceBreakPropertyStr

/-!
  ### Emoji Subdirectory
-/

/-- Includes the emoji-data.txt data. -/
def emojiDataMap := Thunk.mk $ parseStrToMapFn emojiDataStr

/-!
  ### Extracted Subdirectory
-/

/-- Includes the DerivedBidiClass.txt string. -/
def derivedBidiClassMap := Thunk.mk $ parseStrToMapFn derivedBidiClassStr

/-- Includes the DerivedJoiningGroup.txt string. -/
def derivedJoiningGroupMap := Thunk.mk $ parseStrToMapFn derivedJoiningGroupStr

/-- Includes the DerivedBinaryProperties.txt string. -/
def derivedBinaryPropertiesMap := Thunk.mk $ parseStrToMapFn derivedBinaryPropertiesStr

/-- Includes the DerivedJoiningType.txt string. -/
def derivedJoiningTypeMap := Thunk.mk $ parseStrToMapFn derivedJoiningTypeStr

/-- Includes the DerivedCombiningClass.txt string. -/
def derivedCombiningClassMap := Thunk.mk $ parseStrToMapFn derivedCombiningClassStr

/-- Includes the DerivedLineBreak.txt string. -/
def derivedLineBreakMap := Thunk.mk $ parseStrToMapFn derivedLineBreakStr

/-- Includes the DerivedDecompositionType.txt string. -/
def derivedDecompositionTypeMap := Thunk.mk $ parseStrToMapFn derivedDecompositionTypeStr

/-- Includes the DerivedName.txt string. -/
def derivedNameMap := Thunk.mk $ parseStrToMapFn derivedNameStr

/-- Includes the DerivedEastAsianWidth.txt string. -/
def derivedEastAsianWidthMap := Thunk.mk $ parseStrToMapFn derivedEastAsianWidthStr

/-- Includes the DerivedNumericType.txt string. -/
def derivedNumericTypeMap := Thunk.mk $ parseStrToMapFn derivedNumericTypeStr

/-- Includes the DerivedGeneralCategory.txt string. -/
def derivedGeneralCategoryMap := Thunk.mk $ parseStrToMapFn derivedGeneralCategoryStr

/-- Includes the DerivedNumericValues.txt string. -/
def derivedNumericValuesMap := Thunk.mk $ parseStrToMapFn derivedNumericValuesStr

/-!
  ### Unihan Subdirectory
-/

/-- Includes the Unihan_DictionaryIndices.txt string. -/
def unihanDictionaryIndicesMap := Thunk.mk $ parseStrToMapFn unihanDictionaryIndicesStr

/-- Includes the Unihan_OtherMappings.txt string. -/
def unihanOtherMappingsMap := Thunk.mk $ parseStrToMapFn unihanOtherMappingsStr

/-- Includes the Unihan_DictionaryLikeData.txt string. -/
def unihanDictionaryLikeDataMap := Thunk.mk $ parseStrToMapFn unihanDictionaryLikeDataStr

/-- Includes the Unihan_RadicalStrokeCounts.txt string. -/
def unihanRadicalStrokeCountsMap := Thunk.mk $ parseStrToMapFn unihanRadicalStrokeCountsStr

/-- Includes the Unihan_IRGSources.txt string. -/
def unihanIRGSourcesMap := Thunk.mk $ parseStrToMapFn unihanIRGSourcesStr

/-- Includes the Unihan_Readings.txt string. -/
def unihanReadingsMap := Thunk.mk $ parseStrToMapFn unihanReadingsStr

/-- Includes the Unihan_NumericValues.txt string. -/
def unihanNumericValuesMap := Thunk.mk $ parseStrToMapFn unihanNumericValuesStr

/-- Includes the Unihan_Variants.txt string. -/
def unihanVariantsMap := Thunk.mk $ parseStrToMapFn unihanVariantsStr

end Unicode


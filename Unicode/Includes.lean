import Lean
import Std.Data.HashMap

namespace Unicode

open Lean System IO Lean.Elab.Term Std FS

/-!
  # Include UCD Data

  This modules includes all UCD 14.0 data:

  - `unicodeDataMap`: UnicodeData.txt
-/

/-!
  ## The `include_str%` Macro

  This macro is copied from https://github.com/leanprover/doc-gen4/blob/main/DocGen4/IncludeStr.lean by Henrik Böving
-/

deriving instance DecidableEq for FileType

/--
  Traverse all subdirectories fo `f` to find if one satisfies `p`.
-/
partial def traverseDir (f : FilePath) (p : FilePath → IO Bool) : IO (Option FilePath) := do
  if (← p f) then
    return f
  for d in (← System.FilePath.readDir f) do
    let subDir := d.path
    let metadata ← subDir.metadata
    if metadata.type = FileType.dir then
      if let some p ← traverseDir subDir p then
        return p
  return none

syntax (name := includeStr) "include_str%" str : term

@[termElab includeStr] def includeStrImpl : TermElab := λ stx expectedType? => do
  let str := stx[1].isStrLit?.get!
  let srcPath := (FilePath.mk (← read).fileName)
  let currentDir ← IO.currentDir
  -- HACK: Currently we cannot get current file path in VSCode, we have to traversely find the matched subdirectory in the current directory.
  if let some path ← match srcPath.parent with
  | some p => pure $ some $ p / str
  | none => do
    let foundDir ← traverseDir currentDir λ p => p / str |>.pathExists 
    pure $ foundDir.map (· / str)
  then 
    if ←path.pathExists then
      if ←path.isDir then
        throwError s!"{str} is a directory"
      else
        let content ← FS.readFile path
        pure $ mkStrLit content
    else
      throwError s!"{path} does not exist as a file"
  else
    throwError s!"No such file in whole directory: {str}"

/-!
  ## Included Raw Strings

  ### UCD Main Directory
-/

/-- Includes the ArabicShaping.txt string. -/
def arabicShapingStr := include_str% "../UCD/ArabicShaping.txt"

/-- Includes the NamedSequences.txt string. -/
def namedSequencesStr := include_str% "../UCD/NamedSequences.txt"

/-- Includes the BidiBrackets.txt string. -/
def bidiBracketsStr := include_str% "../UCD/BidiBrackets.txt"

/-- Includes the NamedSequencesProv.txt string. -/
def namedSequencesProvStr := include_str% "../UCD/NamedSequencesProv.txt"

/-- Includes the BidiCharacterTest.txt string. -/
def bidiCharacterTestStr := include_str% "../UCD/BidiCharacterTest.txt"

/-- Includes the NamesList.txt string. -/
def namesListStr := include_str% "../UCD/NamesList.txt"

/-- Includes the BidiMirroring.txt string. -/
def bidiMirroringStr := include_str% "../UCD/BidiMirroring.txt"

/-- Includes the NormalizationCorrections.txt string. -/
def normalizationCorrectionsStr := include_str% "../UCD/NormalizationCorrections.txt"

/-- Includes the BidiTest.txt string. -/
def bidiTestStr := include_str% "../UCD/BidiTest.txt"

/-- Includes the NormalizationTest.txt string. -/
def normalizationTestStr := include_str% "../UCD/NormalizationTest.txt"

/-- Includes the Blocks.txt string. -/
def blocksStr := include_str% "../UCD/Blocks.txt"

/-- Includes the NushuSources.txt string. -/
def nushuSourcesStr := include_str% "../UCD/NushuSources.txt"

/-- Includes the CJKRadicals.txt string. -/
def cjkRadicalsStr := include_str% "../UCD/CJKRadicals.txt"

/-- Includes the PropList.txt string. -/
def propListStr := include_str% "../UCD/PropList.txt"

/-- Includes the CaseFolding.txt string. -/
def caseFoldingStr := include_str% "../UCD/CaseFolding.txt"

/-- Includes the PropertyAliases.txt string. -/
def propertyAliasesStr := include_str% "../UCD/PropertyAliases.txt"

/-- Includes the CompositionExclusions.txt string. -/
def compositionExclusionsStr := include_str% "../UCD/CompositionExclusions.txt"
  
/-- Includes the PropertyValueAliases.txt string. -/
def propertyValueAliasesStr := include_str% "../UCD/PropertyValueAliases.txt"

/-- Includes the DerivedAge.txt string. -/
def derivedAgeStr := include_str% "../UCD/DerivedAge.txt"

/-- Includes the ScriptExtensions.txt string. -/
def scriptExtensionsStr := include_str% "../UCD/ScriptExtensions.txt"

/-- Includes the DerivedCoreProperties.txt string. -/
def derivedCorePropertiesStr := include_str% "../UCD/DerivedCoreProperties.txt"

/-- Includes the Scripts.txt string. -/
def scriptsStr := include_str% "../UCD/Scripts.txt"

/-- Includes the DerivedNormalizationProps.txt string. -/
def derivedNormalizationPropsStr := include_str% "../UCD/DerivedNormalizationProps.txt"

/-- Includes the SpecialCasing.txt string. -/
def specialCasingStr := include_str% "../UCD/SpecialCasing.txt"

/-- Includes the EastAsianWidth.txt string. -/
def eastAsianWidthStr := include_str% "../UCD/EastAsianWidth.txt"

/-- Includes the StandardizedVariants.txt string. -/
def standardizedVariantsStr := include_str% "../UCD/StandardizedVariants.txt"

/-- Includes the EmojiSources.txt string. -/
def emojiSourcesStr := include_str% "../UCD/EmojiSources.txt"

/-- Includes the TangutSources.txt string. -/
def tangutSourcesStr := include_str% "../UCD/TangutSources.txt"

/-- Includes the EquivalentUnifiedIdeograph.txt string. -/
def equivalentUnifiedIdeographStr := include_str% "../UCD/EquivalentUnifiedIdeograph.txt"

/-- Includes the USourceData.txt string. -/
def uSourceDataStr := include_str% "../UCD/USourceData.txt"

/-- Includes the HangulSyllableType.txt string. -/
def hangulSyllableTypeStr := include_str% "../UCD/HangulSyllableType.txt"

/-- Includes the UnicodeData.txt string. See `unicodeDataMap`. -/
def unicodeDataStr := include_str% "../UCD/UnicodeData.txt"

/-- Includes the Index.txt string. -/
def indexStr := include_str% "../UCD/Index.txt"

/-- Includes the IndicPositionalCategory.txt string. -/
def indicPositionalCategoryStr := include_str% "../UCD/IndicPositionalCategory.txt"

/-- Includes the VerticalOrientation.txt string. -/
def verticalOrientationStr := include_str% "../UCD/VerticalOrientation.txt"

/-- Includes the IndicSyllabicCategory.txt string. -/
def indicSyllabicCategoryStr := include_str% "../UCD/IndicSyllabicCategory.txt"

/-- Includes the Jamo.txt string. -/
def jamoStr := include_str% "../UCD/Jamo.txt"

/-- Includes the LineBreak.txt string. -/
def lineBreakStr := include_str% "../UCD/LineBreak.txt"

/-- Includes the NameAliases.txt string. -/
def nameAliasesStr := include_str% "../UCD/NameAliases.txt"

/-!
  ### Auxiliary Subdirectory
-/

/-- Includes the GraphemeBreakProperty.txt string. -/
def graphemeBreakPropertyStr := include_str% "../UCD/auxiliary/GraphemeBreakProperty.txt"

/-- Includes the GraphemeBreakTest.txt string. -/
def graphemeBreakTestStr := include_str% "../UCD/auxiliary/GraphemeBreakTest.txt"

/-- Includes the WordBreakProperty.txt string. -/
def wordBreakPropertyStr := include_str% "../UCD/auxiliary/WordBreakProperty.txt"
  
/-- Includes the LineBreakTest.txt string. -/
def lineBreakTestStr := include_str% "../UCD/auxiliary/LineBreakTest.txt"

/-- Includes the WordBreakTest.txt string. -/
def wordBreakTestStr := include_str% "../UCD/auxiliary/WordBreakTest.txt"

/-- Includes the SentenceBreakProperty.txt string. -/
def sentenceBreakPropertyStr := include_str% "../UCD/auxiliary/SentenceBreakProperty.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def sentenceBreakTestStr := include_str% "../UCD/auxiliary/SentenceBreakTest.txt"

/-!
  ### Emoji Subdirectory
-/

/-- Includes the emoji-data.txt string. -/
def emojiDataStr := include_str% "../UCD/emoji/emoji-data.txt"

/-- Includes the emoji-variation-sequences.txt string. -/
def emojiVariationSequencesStr := include_str% "../UCD/emoji/emoji-variation-sequences.txt"

/-!
  ### Extracted Subdirectory
-/

/-- Includes the SentenceBreakTest.txt string. -/
def derivedBidiClassStr := include_str% "../UCD/extracted/DerivedBidiClass.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedJoiningGroupStr := include_str% "../UCD/extracted/DerivedJoiningGroup.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedBinaryPropertiesStr := include_str% "../UCD/extracted/DerivedBinaryProperties.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedJoiningTypeStr := include_str% "../UCD/extracted/DerivedJoiningType.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedCombiningClassStr := include_str% "../UCD/extracted/DerivedCombiningClass.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedLineBreakStr := include_str% "../UCD/extracted/DerivedLineBreak.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedDecompositionTypeStr := include_str% "../UCD/extracted/DerivedDecompositionType.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedNameStr := include_str% "../UCD/extracted/DerivedName.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedEastAsianWidthStr := include_str% "../UCD/extracted/DerivedEastAsianWidth.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedNumericTypeStr := include_str% "../UCD/extracted/DerivedNumericType.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedGeneralCategoryStr := include_str% "../UCD/extracted/DerivedGeneralCategory.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def derivedNumericValuesStr := include_str% "../UCD/extracted/DerivedNumericValues.txt"

/-!
  ### Unihan Subdirectory
-/

/-- Includes the SentenceBreakTest.txt string. -/
def unihanDictionaryIndicesStr := include_str% "../UCD/Unihan/Unihan_DictionaryIndices.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanOtherMappingsStr := include_str% "../UCD/Unihan/Unihan_OtherMappings.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanDictionaryLikeDataStr := include_str% "../UCD/Unihan/Unihan_DictionaryLikeData.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanRadicalStrokeCountsStr := include_str% "../UCD/Unihan/Unihan_RadicalStrokeCounts.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanIRGSourcesStr := include_str% "../UCD/Unihan/Unihan_IRGSources.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanReadingsStr := include_str% "../UCD/Unihan/Unihan_Readings.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanNumericValuesStr := include_str% "../UCD/Unihan/Unihan_NumericValues.txt"

/-- Includes the SentenceBreakTest.txt string. -/
def unihanVariantsStr := include_str% "../UCD/Unihan/Unihan_Variants.txt"

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
    | _ => panic! "Invalid hex digit"
    foldlHexDigits acc d := 16 * acc + d

/-- Make `Char` `Hashable` as key of `HashMap`. -/
instance : Hashable Char := ⟨ λ c => String.hash $ Char.toString c ⟩ 

/-- Parse data file `String` into `HashMap`, the unit in parameter is left for `Thunk`. -/
def parseStrToMapFn (s : String) (unit : Unit) : HashMap Char (List String) := Id.run do
  let mut map := HashMap.empty
  for line in unicodeDataStr.splitOn "\n" |>.filter (· ≠ "") do
    let splits := line.splitOn ";" |>.map String.trim
    let char := Char.ofNat $ decodeHex! $ splits.get! 0
    map := map.insert char (splits.tail!)
  return map

/-- Includes the UnicodeData.txt data. -/
def unicodeDataMap : Thunk (HashMap Char (List String)) := ⟨ parseStrToMapFn unicodeDataStr ⟩ 

end Unicode
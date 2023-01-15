
/-!
  ## Included Raw Strings
-/

namespace Unicode.Data

/-!
  ### UCD Main Directory
-/

/-- Includes the ArabicShaping.txt string. -/
def arabicShapingStr := include_str "../../UCD/ArabicShaping.txt"

/-- Includes the BidiBrackets.txt string. -/
def bidiBracketsStr := include_str "../../UCD/BidiBrackets.txt"

/-- Includes the BidiMirroring.txt string. -/
def bidiMirroringStr := include_str "../../UCD/BidiMirroring.txt"

/-- Includes the NormalizationCorrections.txt string. -/
def normalizationCorrectionsStr := include_str "../../UCD/NormalizationCorrections.txt"

/-- Includes the Blocks.txt string. -/
def blocksStr := include_str "../../UCD/Blocks.txt"

/-- Includes the NushuSources.txt string. -/
def nushuSourcesStr := include_str "../../UCD/NushuSources.txt"

/-- Includes the PropList.txt string. -/
def propListStr := include_str "../../UCD/PropList.txt"

/-- Includes the CaseFolding.txt string. -/
def caseFoldingStr := include_str "../../UCD/CaseFolding.txt"

/-- Includes the CompositionExclusions.txt string. -/
def compositionExclusionsStr := include_str "../../UCD/CompositionExclusions.txt"

/-- Includes the DerivedAge.txt string. -/
def derivedAgeStr := include_str "../../UCD/DerivedAge.txt"

/-- Includes the ScriptExtensions.txt string. -/
def scriptExtensionsStr := include_str "../../UCD/ScriptExtensions.txt"

/-- Includes the DerivedCoreProperties.txt string. -/
def derivedCorePropertiesStr := include_str "../../UCD/DerivedCoreProperties.txt"

/-- Includes the Scripts.txt string. -/
def scriptsStr := include_str "../../UCD/Scripts.txt"

/-- Includes the DerivedNormalizationProps.txt string. -/
def derivedNormalizationPropsStr := include_str "../../UCD/DerivedNormalizationProps.txt"

/-- Includes the SpecialCasing.txt string. -/
def specialCasingStr := include_str "../../UCD/SpecialCasing.txt"

/-- Includes the EastAsianWidth.txt string. -/
def eastAsianWidthStr := include_str "../../UCD/EastAsianWidth.txt"

/-- Includes the EquivalentUnifiedIdeograph.txt string. -/
def equivalentUnifiedIdeographStr := include_str "../../UCD/EquivalentUnifiedIdeograph.txt"

/-- Includes the HangulSyllableType.txt string. -/
def hangulSyllableTypeStr := include_str "../../UCD/HangulSyllableType.txt"

/-- Includes the UnicodeData.txt string. See `unicodeDataMap`. -/
def unicodeDataStr := include_str "../../UCD/UnicodeData.txt"

/-- Includes the IndicPositionalCategory.txt string. -/
def indicPositionalCategoryStr := include_str "../../UCD/IndicPositionalCategory.txt"

/-- Includes the VerticalOrientation.txt string. -/
def verticalOrientationStr := include_str "../../UCD/VerticalOrientation.txt"

/-- Includes the IndicSyllabicCategory.txt string. -/
def indicSyllabicCategoryStr := include_str "../../UCD/IndicSyllabicCategory.txt"

/-- Includes the Jamo.txt string. -/
def jamoStr := include_str "../../UCD/Jamo.txt"

/-- Includes the LineBreak.txt string. -/
def lineBreakStr := include_str "../../UCD/LineBreak.txt"

/-- Includes the NameAliases.txt string. -/
def nameAliasesStr := include_str "../../UCD/NameAliases.txt"

/-!
  ### Auxiliary Subdirectory
-/

/-- Includes the GraphemeBreakProperty.txt string. -/
def graphemeBreakPropertyStr := include_str "../../UCD/auxiliary/GraphemeBreakProperty.txt"

/-- Includes the WordBreakProperty.txt string. -/
def wordBreakPropertyStr := include_str "../../UCD/auxiliary/WordBreakProperty.txt"

/-- Includes the SentenceBreakProperty.txt string. -/
def sentenceBreakPropertyStr := include_str "../../UCD/auxiliary/SentenceBreakProperty.txt"

/-!
  ### Emoji Subdirectory
-/

/-- Includes the emoji-data.txt string. -/
def emojiDataStr := include_str "../../UCD/emoji/emoji-data.txt"

/-!
  ### Extracted Subdirectory
-/

/-- Includes the DerivedBidiClass.txt string. -/
def derivedBidiClassStr := include_str "../../UCD/extracted/DerivedBidiClass.txt"

/-- Includes the DerivedJoiningGroup.txt string. -/
def derivedJoiningGroupStr := include_str "../../UCD/extracted/DerivedJoiningGroup.txt"

/-- Includes the DerivedBinaryProperties.txt string. -/
def derivedBinaryPropertiesStr := include_str "../../UCD/extracted/DerivedBinaryProperties.txt"

/-- Includes the DerivedJoiningType.txt string. -/
def derivedJoiningTypeStr := include_str "../../UCD/extracted/DerivedJoiningType.txt"

/-- Includes the DerivedCombiningClass.txt string. -/
def derivedCombiningClassStr := include_str "../../UCD/extracted/DerivedCombiningClass.txt"

/-- Includes the DerivedLineBreak.txt string. -/
def derivedLineBreakStr := include_str "../../UCD/extracted/DerivedLineBreak.txt"

/-- Includes the DerivedDecompositionType.txt string. -/
def derivedDecompositionTypeStr := include_str "../../UCD/extracted/DerivedDecompositionType.txt"

/-- Includes the DerivedName.txt string. -/
def derivedNameStr := include_str "../../UCD/extracted/DerivedName.txt"

/-- Includes the DerivedEastAsianWidth.txt string. -/
def derivedEastAsianWidthStr := include_str "../../UCD/extracted/DerivedEastAsianWidth.txt"

/-- Includes the DerivedNumericType.txt string. -/
def derivedNumericTypeStr := include_str "../../UCD/extracted/DerivedNumericType.txt"

/-- Includes the DerivedGeneralCategory.txt string. -/
def derivedGeneralCategoryStr := include_str "../../UCD/extracted/DerivedGeneralCategory.txt"

/-- Includes the DerivedNumericValues.txt string. -/
def derivedNumericValuesStr := include_str "../../UCD/extracted/DerivedNumericValues.txt"

/-!
  ### Unihan Subdirectory
-/

/-- Includes the Unihan_DictionaryIndices.txt string. -/
def unihanDictionaryIndicesStr := include_str "../../UCD/Unihan/Unihan_DictionaryIndices.txt"

/-- Includes the Unihan_OtherMappings.txt string. -/
def unihanOtherMappingsStr := include_str "../../UCD/Unihan/Unihan_OtherMappings.txt"

/-- Includes the Unihan_DictionaryLikeData.txt string. -/
def unihanDictionaryLikeDataStr := include_str "../../UCD/Unihan/Unihan_DictionaryLikeData.txt"

/-- Includes the Unihan_RadicalStrokeCounts.txt string. -/
def unihanRadicalStrokeCountsStr := include_str "../../UCD/Unihan/Unihan_RadicalStrokeCounts.txt"

/-- Includes the Unihan_IRGSources.txt string. -/
def unihanIRGSourcesStr := include_str "../../UCD/Unihan/Unihan_IRGSources.txt"

/-- Includes the Unihan_Readings.txt string. -/
def unihanReadingsStr := include_str "../../UCD/Unihan/Unihan_Readings.txt"

/-- Includes the Unihan_NumericValues.txt string. -/
def unihanNumericValuesStr := include_str "../../UCD/Unihan/Unihan_NumericValues.txt"

/-- Includes the Unihan_Variants.txt string. -/
def unihanVariantsStr := include_str "../../UCD/Unihan/Unihan_Variants.txt"

end Unicode.Data

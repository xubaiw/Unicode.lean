import Std.Data.HashMap
import Unicode.Includes

open Std

open Unicode

def printSize (t : Thunk (HashMap Char (List String))) : IO Unit :=
  IO.println t.get.size

def main : IO Unit := do
  printSize arabicShapingMap
  printSize bidiBracketsMap
  printSize bidiMirroringMap
  printSize normalizationCorrectionsMap
  printSize blocksMap
  printSize nushuSourcesMap
  printSize propListMap
  printSize caseFoldingMap
  printSize compositionExclusionsMap
  printSize derivedAgeMap
  printSize scriptExtensionsMap
  printSize derivedCorePropertiesMap
  printSize scriptsMap
  printSize derivedNormalizationPropsMap
  printSize specialCasingMap
  printSize eastAsianWidthMap
  printSize equivalentUnifiedIdeographMap
  printSize hangulSyllableTypeMap
  printSize unicodeDataMap
  printSize indicPositionalCategoryMap
  printSize verticalOrientationMap
  printSize indicSyllabicCategoryMap
  printSize jamoMap
  printSize lineBreakMap
  printSize nameAliasesMap
  printSize graphemeBreakPropertyMap
  printSize wordBreakPropertyMap
  printSize sentenceBreakPropertyMap
  printSize emojiDataMap
  printSize derivedBidiClassMap
  printSize derivedJoiningGroupMap
  printSize derivedBinaryPropertiesMap
  printSize derivedJoiningTypeMap
  printSize derivedCombiningClassMap
  printSize derivedLineBreakMap
  printSize derivedDecompositionTypeMap
  printSize derivedNameMap
  printSize derivedEastAsianWidthMap
  printSize derivedNumericTypeMap
  printSize derivedGeneralCategoryMap
  printSize derivedNumericValuesMap
  -- printSize unihanDictionaryIndicesMap -- stack overflow
  -- printSize unihanOtherMappingsMap -- stack overflow
  printSize unihanDictionaryLikeDataMap
  printSize unihanRadicalStrokeCountsMap
  -- printSize unihanIRGSourcesMap -- stack overflow
  -- printSize unihanReadingsMap -- stack overflow
  printSize unihanNumericValuesMap
  printSize unihanVariantsMap
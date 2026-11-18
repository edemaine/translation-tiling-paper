import TranslationTiling.Compiler.SmallTileData0
import TranslationTiling.Compiler.SmallTileData1
import TranslationTiling.Compiler.SmallTileData2
import TranslationTiling.Compiler.SmallTileData3
import TranslationTiling.Compiler.SmallTileData4
import TranslationTiling.Compiler.SmallTileData5
import TranslationTiling.Compiler.SmallTileData6
import TranslationTiling.Compiler.SmallTileData7
import TranslationTiling.Compiler.SmallTileData8
import TranslationTiling.Compiler.SmallTileData9
import TranslationTiling.Compiler.SmallTileData10
import TranslationTiling.Compiler.SmallTileData11
import TranslationTiling.Compiler.SmallTileData12
import TranslationTiling.Compiler.SmallTileData13
import TranslationTiling.Compiler.SmallTileData14
import TranslationTiling.Compiler.SmallTileData15
namespace TranslationTiling.Compiler.SmallTile
structure CheckedRow where
  mask : ℕ
  certificates : List Certificate
  valid : ∀ i : Fin 128, Valid mask (masks.getD i.val 0)
    (certificates.getD i.val (.obstruction 0))=true
def checkedRows : List CheckedRow :=
  [⟨0,certificates0,certificates0_valid⟩,
   ⟨1,certificates1,certificates1_valid⟩,
   ⟨2,certificates2,certificates2_valid⟩,
   ⟨3,certificates3,certificates3_valid⟩,
   ⟨4,certificates4,certificates4_valid⟩,
   ⟨5,certificates5,certificates5_valid⟩,
   ⟨6,certificates6,certificates6_valid⟩,
   ⟨7,certificates7,certificates7_valid⟩,
   ⟨8,certificates8,certificates8_valid⟩,
   ⟨9,certificates9,certificates9_valid⟩,
   ⟨10,certificates10,certificates10_valid⟩,
   ⟨12,certificates12,certificates12_valid⟩,
   ⟨14,certificates14,certificates14_valid⟩,
   ⟨16,certificates16,certificates16_valid⟩,
   ⟨17,certificates17,certificates17_valid⟩,
   ⟨18,certificates18,certificates18_valid⟩,
   ⟨20,certificates20,certificates20_valid⟩,
   ⟨21,certificates21,certificates21_valid⟩,
   ⟨24,certificates24,certificates24_valid⟩,
   ⟨27,certificates27,certificates27_valid⟩,
   ⟨28,certificates28,certificates28_valid⟩,
   ⟨32,certificates32,certificates32_valid⟩,
   ⟨33,certificates33,certificates33_valid⟩,
   ⟨34,certificates34,certificates34_valid⟩,
   ⟨35,certificates35,certificates35_valid⟩,
   ⟨36,certificates36,certificates36_valid⟩,
   ⟨40,certificates40,certificates40_valid⟩,
   ⟨42,certificates42,certificates42_valid⟩,
   ⟨45,certificates45,certificates45_valid⟩,
   ⟨48,certificates48,certificates48_valid⟩,
   ⟨49,certificates49,certificates49_valid⟩,
   ⟨54,certificates54,certificates54_valid⟩,
   ⟨56,certificates56,certificates56_valid⟩,
   ⟨63,certificates63,certificates63_valid⟩,
   ⟨64,certificates64,certificates64_valid⟩,
   ⟨65,certificates65,certificates65_valid⟩,
   ⟨66,certificates66,certificates66_valid⟩,
   ⟨68,certificates68,certificates68_valid⟩,
   ⟨70,certificates70,certificates70_valid⟩,
   ⟨72,certificates72,certificates72_valid⟩,
   ⟨73,certificates73,certificates73_valid⟩,
   ⟨74,certificates74,certificates74_valid⟩,
   ⟨76,certificates76,certificates76_valid⟩,
   ⟨78,certificates78,certificates78_valid⟩,
   ⟨80,certificates80,certificates80_valid⟩,
   ⟨81,certificates81,certificates81_valid⟩,
   ⟨82,certificates82,certificates82_valid⟩,
   ⟨84,certificates84,certificates84_valid⟩,
   ⟨96,certificates96,certificates96_valid⟩,
   ⟨97,certificates97,certificates97_valid⟩,
   ⟨98,certificates98,certificates98_valid⟩,
   ⟨100,certificates100,certificates100_valid⟩,
   ⟨112,certificates112,certificates112_valid⟩,
   ⟨113,certificates113,certificates113_valid⟩,
   ⟨118,certificates118,certificates118_valid⟩,
   ⟨128,certificates128,certificates128_valid⟩,
   ⟨129,certificates129,certificates129_valid⟩,
   ⟨130,certificates130,certificates130_valid⟩,
   ⟨132,certificates132,certificates132_valid⟩,
   ⟨133,certificates133,certificates133_valid⟩,
   ⟨136,certificates136,certificates136_valid⟩,
   ⟨137,certificates137,certificates137_valid⟩,
   ⟨138,certificates138,certificates138_valid⟩,
   ⟨140,certificates140,certificates140_valid⟩,
   ⟨144,certificates144,certificates144_valid⟩,
   ⟨145,certificates145,certificates145_valid⟩,
   ⟨146,certificates146,certificates146_valid⟩,
   ⟨148,certificates148,certificates148_valid⟩,
   ⟨149,certificates149,certificates149_valid⟩,
   ⟨160,certificates160,certificates160_valid⟩,
   ⟨161,certificates161,certificates161_valid⟩,
   ⟨162,certificates162,certificates162_valid⟩,
   ⟨164,certificates164,certificates164_valid⟩,
   ⟨168,certificates168,certificates168_valid⟩,
   ⟨170,certificates170,certificates170_valid⟩,
   ⟨173,certificates173,certificates173_valid⟩,
   ⟨192,certificates192,certificates192_valid⟩,
   ⟨195,certificates195,certificates195_valid⟩,
   ⟨196,certificates196,certificates196_valid⟩,
   ⟨216,certificates216,certificates216_valid⟩,
   ⟨219,certificates219,certificates219_valid⟩,
   ⟨220,certificates220,certificates220_valid⟩,
   ⟨224,certificates224,certificates224_valid⟩,
   ⟨227,certificates227,certificates227_valid⟩,
   ⟨228,certificates228,certificates228_valid⟩,
   ⟨256,certificates256,certificates256_valid⟩,
   ⟨257,certificates257,certificates257_valid⟩,
   ⟨258,certificates258,certificates258_valid⟩,
   ⟨259,certificates259,certificates259_valid⟩,
   ⟨260,certificates260,certificates260_valid⟩,
   ⟨264,certificates264,certificates264_valid⟩,
   ⟨265,certificates265,certificates265_valid⟩,
   ⟨266,certificates266,certificates266_valid⟩,
   ⟨268,certificates268,certificates268_valid⟩,
   ⟨272,certificates272,certificates272_valid⟩,
   ⟨273,certificates273,certificates273_valid⟩,
   ⟨274,certificates274,certificates274_valid⟩,
   ⟨276,certificates276,certificates276_valid⟩,
   ⟨280,certificates280,certificates280_valid⟩,
   ⟨283,certificates283,certificates283_valid⟩,
   ⟨284,certificates284,certificates284_valid⟩,
   ⟨288,certificates288,certificates288_valid⟩,
   ⟨289,certificates289,certificates289_valid⟩,
   ⟨290,certificates290,certificates290_valid⟩,
   ⟨291,certificates291,certificates291_valid⟩,
   ⟨292,certificates292,certificates292_valid⟩,
   ⟨320,certificates320,certificates320_valid⟩,
   ⟨322,certificates322,certificates322_valid⟩,
   ⟨325,certificates325,certificates325_valid⟩,
   ⟨336,certificates336,certificates336_valid⟩,
   ⟨338,certificates338,certificates338_valid⟩,
   ⟨341,certificates341,certificates341_valid⟩,
   ⟨360,certificates360,certificates360_valid⟩,
   ⟨362,certificates362,certificates362_valid⟩,
   ⟨365,certificates365,certificates365_valid⟩,
   ⟨384,certificates384,certificates384_valid⟩,
   ⟨385,certificates385,certificates385_valid⟩,
   ⟨390,certificates390,certificates390_valid⟩,
   ⟨392,certificates392,certificates392_valid⟩,
   ⟨393,certificates393,certificates393_valid⟩,
   ⟨398,certificates398,certificates398_valid⟩,
   ⟨432,certificates432,certificates432_valid⟩,
   ⟨433,certificates433,certificates433_valid⟩,
   ⟨438,certificates438,certificates438_valid⟩,
   ⟨448,certificates448,certificates448_valid⟩,
   ⟨455,certificates455,certificates455_valid⟩,
   ⟨504,certificates504,certificates504_valid⟩,
   ⟨511,certificates511,certificates511_valid⟩]
theorem checkedRows_masks : checkedRows.map CheckedRow.mask=masks := rfl
theorem exists_certificate {H V : ℕ} (hH : H∈masks) (hV : V∈masks) :
    ∃ c, Valid H V c=true := by
  rw [←checkedRows_masks] at hH
  obtain ⟨r,_,hr⟩ := List.mem_map.mp hH
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hV
  have hi' : i<128 := by simpa only [masks_length] using hi
  refine ⟨r.certificates.getD i (.obstruction 0),?_⟩
  rw [←hr,←he,←List.getD_eq_getElem _ _ hi]
  exact r.valid ⟨i,hi'⟩
end TranslationTiling.Compiler.SmallTile

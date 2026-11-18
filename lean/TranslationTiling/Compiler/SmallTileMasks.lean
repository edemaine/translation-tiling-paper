import TranslationTiling.Compiler.SmallTileCertificate
namespace TranslationTiling.Compiler.SmallTile
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def masks : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 17, 18, 20, 21, 24, 27, 28, 32, 33, 34, 35, 36, 40, 42, 45, 48, 49, 54, 56, 63, 64, 65, 66, 68, 70, 72, 73, 74, 76, 78, 80, 81, 82, 84, 96, 97, 98, 100, 112, 113, 118, 128, 129, 130, 132, 133, 136, 137, 138, 140, 144, 145, 146, 148, 149, 160, 161, 162, 164, 168, 170, 173, 192, 195, 196, 216, 219, 220, 224, 227, 228, 256, 257, 258, 259, 260, 264, 265, 266, 268, 272, 273, 274, 276, 280, 283, 284, 288, 289, 290, 291, 292, 320, 322, 325, 336, 338, 341, 360, 362, 365, 384, 385, 390, 392, 393, 398, 432, 433, 438, 448, 455, 504, 511]
theorem masks_length : masks.length=128 := by decide +kernel
theorem matrixCode_mem : ∀ r : Matrix, Rectangular r → matrixCode r∈masks := by decide +kernel
end TranslationTiling.Compiler.SmallTile

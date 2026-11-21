import TranslationTiling.FiniteCompiler.Effective.SharedBatchDeck
import TranslationTiling.FiniteCompiler.Effective.SharedOrdinaryOffsets

namespace TranslationTiling.FiniteCompiler.SharedCoordinates

open Compiler.Effective TranslationTiling.FiniteCompiler.Effective
open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] (L : Layout I)
variable {a b : ℕ} [NeZero a] [NeZero b]

def compactOffset (i : I) (s : ℕ) (j : OrdinaryIndex (L.lowSize i) a b) : Plane :=
  let h := compactFirst ((a,b,L.lowSize i),ordinaryIndexCode j)
  (h,-(s:ℤ)*h)

/-- The executable ordinary test realizes the checked activation equation. -/
theorem compactCodes_tiles_iff [NeZero (order L)]
    (crt : ZMod (order L) ≃+* Factor L) (i : I) (s : ℕ)
    (ψ : Factor L →+ ZMod a × ZMod b)
    (hψ : ∀ n : ℕ, ψ (decode L n) = ((n : ZMod a),(n : ZMod b)))
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hrA : Nat.Coprime (L.lowSize i) a) (hrB : Nat.Coprime (L.lowSize i*a) b)
    (hsep : ((2 : ZMod a),(2 : ZMod b)) ≠ (-1,-1))
    (rs : List ℕ) (hr : ∀ r, r ∈ rs ↔ ∃ j, j ≠ i ∧ L.lowSize j = r)
    (o : Outputs L)
    (htarget : ∀ x : Base L, ∀ c : ZMod a × ZMod b, ∀ d : Low L i,
      ∃ v : Ambient L, baseProjection L v = x ∧ ψ v.2 = c ∧ highCoordinate L i v = d) :
    let src := fun x j => activationSource L i (compactOffset L i s j) j.1 x
    Tiles ((compactCodes ((order L,rs),(L.lowSize i,a,b,1225)) s).toFinset.image (decodePoint L))
        (Set.range (point L o)) ↔
      ∀ x, Function.Bijective (fun j =>
        (ψ (point L o (src x j)).2 + shift a b j.2, o.high (src x j) i)) := by
  let J := OrdinaryIndex (L.lowSize i) a b
  let js := (Finset.univ : Finset J).toList
  let ω : J → Plane := compactOffset L i s
  let e : J → ZMod a × ZMod b := fun j => shift a b j.2
  have hbatch (j : J) :
      compactBatch ((order L,rs),(L.lowSize i,a,b,1225)) s (ordinaryIndexCode j) =
      activationBatchCodes ((order L,rs),(L.lowSize i,a,b,1225),ω j,((e j).1.val,(e j).2.val),true) :=
    rfl
  have he : (compactCodes ((order L,rs),(L.lowSize i,a,b,1225)) s).toFinset =
      (batchDeck L i rs js ω e).toFinset := by
    ext p
    simp only [List.mem_toFinset,compactCodes,batchDeck,List.mem_flatMap]
    constructor
    · rintro ⟨c,hc,hp⟩
      obtain ⟨j,rfl⟩ := (activationIndices_iff ha hb c).mp hc
      exact ⟨j,by simp [js],hbatch j ▸ hp⟩
    · rintro ⟨j,_,hp⟩
      exact ⟨ordinaryIndexCode j,(activationIndices_iff ha hb _).mpr ⟨j,rfl⟩,(hbatch j).symm ▸ hp⟩
  have hω : Function.Injective ω := fun j j' h =>
    compactFirst_injective ha hb hrA hrB hsep (congrArg Prod.fst h)
  have hl (j : J) : ((ω j).1 : Low L i) = j.1 :=
    congrArg (fun z : (Low L i × ZMod a) × ZMod b => z.1.1) (compactFirst_residues hrA hrB j)
  rw [he]
  simpa only [hl,e,ω] using
    tiles_batchDeck_iff L crt ψ hψ i rs hr js (fun j => by simp [js]) ω hω e o htarget

end
end TranslationTiling.FiniteCompiler.SharedCoordinates

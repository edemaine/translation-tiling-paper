import TranslationTiling.FiniteCompiler.Effective.FreshStack
import TranslationTiling.FiniteCompiler.Effective.StackSupport
import TranslationTiling.FiniteCompiler.CyclicFactorCRT
import TranslationTiling.FiniteCompiler.GraphTests

namespace TranslationTiling.Compiler
open Effective
open scoped Classical

/-- A full vertical coset at horizontal coordinate zero. -/
def HasColumn (d : CyclicTileData) (U : ℕ) : Prop :=
  ∃ c : ZMod d.1, ∀ k : ℤ, ((0 : Plane), c+((U:ℤ)*k : ℤ))∈cyclicTileSet d.1 d.2

theorem stack_hasColumn (N P : ℕ) (Fs : List CyclicTile) (c : PartitionCertificate)
    (hc : PartitionValid (Fs.length-1) P c) (hcop : Nat.Coprime N c.1)
    (hN : 0<N) (i : Fin Fs.length) (R : ℕ)
    (hR : ∀ k : ℤ, (((0:Plane), ((R:ℤ)*k : ℤ)) : Plane × ZMod N)∈
      cyclicTileSet N (Fs.getD i.val [])) :
    HasColumn (N*c.1,stackCodes (N,c,Fs)) (R*c.1) := by
  letI : NeZero N := ⟨hN.ne'⟩
  letI : NeZero c.1 := ⟨hc.1.ne_zero⟩
  have hlen : Fs.length-1+1=Fs.length := by have := i.isLt; omega
  obtain ⟨x,hx,_,_,hx'⟩ := hc.2.2.2.2 i.val (by simpa [hlen] using i.isLt) 0
    (List.mem_range.mpr hc.1.pos)
  let j : ZMod c.1 := x
  have hj : j ∈ stackParts Fs.length c.1 c.2 i := by
    simp only [stackParts,Finset.mem_filter,Finset.mem_univ,true_and,j,ZMod.val_natCast,
      Nat.mod_eq_of_lt (List.mem_range.mp hx)]
    exact hx'.1
  let e := ZMod.chineseRemainder hcop
  refine ⟨e.symm (0,j),fun k => ?_⟩
  rw [stackCodes_correct hcop c.2 Fs]
  have he : e (e.symm (0,j)+(((R*c.1:ℕ):ℤ)*k : ℤ)) =
      ((((R:ℤ)*((c.1:ℤ)*k) : ℤ) : ZMod N),j) := by
    rw [map_add,e.apply_symm_apply,map_intCast]
    ext <;> simp [Prod.fst_add,Prod.snd_add,Int.cast_mul,Nat.cast_mul,ZMod.natCast_self,mul_assoc]
  refine Finset.mem_image.mpr
    ⟨(((0:Plane),((R:ℤ)*((c.1:ℤ)*k):ℤ)),j),?_,?_⟩
  · exact Stacking.mem_stack.mpr ⟨i,hR _,hj⟩
  · change ((0:Plane),e.symm _) = _
    exact Prod.ext rfl (e.symm_apply_eq.mpr he.symm)

end TranslationTiling.Compiler

namespace TranslationTiling.FiniteCompiler
open Compiler
open scoped Classical BigOperators
noncomputable section
variable [SeedFrame] {T : System} [AlphabetFamily T] (E : EncodingParameters T)

def inputOrder : ℕ := ∏ i : Channel T, E.r i

theorem inputOrder_pos : 0 < inputOrder E := Finset.prod_pos fun i _ => E.r_pos i

theorem inputOrder_dvd : inputOrder E ∣ E.cyclicOrder := by
  refine ⟨(residueModulus^2)*∏ i : Channel T, E.r i*E.a i*E.b i,?_⟩
  simp only [inputOrder,EncodingParameters.cyclicOrder,EncodingParameters.blockModulus]
  rw [mul_left_comm,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem kernel_column (k : ℤ) :
    (((0:Plane), ((inputOrder E:ℤ)*k : ℤ)) : Plane × ZMod E.cyclicOrder)∈
      (kernelTile E).image (ambientCyclicEquiv E) := by
  let e := ambientCyclicEquiv E
  refine Finset.mem_image.mpr ⟨e.symm _,?_,e.apply_symm_apply _⟩
  apply (mem_kernelTile E _).mpr
  have hz : (e.symm ((0:Plane),((inputOrder E:ℤ)*k : ℤ))).1=0 := rfl
  apply Prod.ext hz
  funext i
  let f : ZMod E.cyclicOrder →+ K E i :=
    (low E i).comp (((AddMonoidHom.fst _ _).comp
      (Pi.evalAddMonoidHom (fun j : Channel T => ZMod ((E.r j)^2) × P E j) i)).comp
        ((AddMonoidHom.snd _ _).comp ((cyclicToFiniteFactor E).toAddMonoidHom)))
  change f (((inputOrder E:ℤ)*k : ℤ) : ZMod E.cyclicOrder)=0
  obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem (fun j : Channel T => E.r j) (Finset.mem_univ i)
  change inputOrder E=E.r i*b at hb
  have hr : ((inputOrder E:ℤ)*k : ℤ) = (E.r i:ℕ) • ((b:ℤ)*k) := by
    rw [hb,Nat.cast_mul,nsmul_eq_mul]
    ring
  have hc := congrArg (fun z : ℤ => (z : ZMod E.cyclicOrder)) hr
  rw [show (((E.r i:ℕ) • ((b:ℤ)*k) : ℤ):ZMod E.cyclicOrder)=
      (E.r i:ℕ) • ((((b:ℤ)*k):ℤ):ZMod E.cyclicOrder) by simp [nsmul_eq_mul]] at hc
  rw [hc,map_nsmul,nsmul_eq_mul,ZMod.natCast_self,zero_mul]

end
end TranslationTiling.FiniteCompiler

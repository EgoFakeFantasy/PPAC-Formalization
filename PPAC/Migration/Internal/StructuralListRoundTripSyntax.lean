import PPAC.Migration.Internal.StructuralListCodeGraph

/-! 实际编码唯一纤维及三重实际见证的解码再编码原码恢复合同。 -/
namespace PPAC.Migration.Internal.StructuralListRoundTripSyntax
open Source SourceAlgebra SourceLogic StructuralListEncodeSyntax StructuralListFieldGraphSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)

def encodingFiber {m} (w f r : Fin m) : Formula m := .ex
  ((encoding w.castSucc f.castSucc r.castSucc (Fin.last m)).conj (.all
    ((encoding w.castSucc.castSucc f.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def roundTripBody {m} (w n : Fin m) : Formula (m+3) :=
  (((hasLength w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj
    (fields w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)).conj
    (encoding w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)))).conj
    (.equal (Fin.last (m+2)) n.castSucc.castSucc.castSucc)

def roundTrip {m} (w n : Fin m) : Formula m := .ex (.ex (.ex (roundTripBody w n)))

theorem encodingFiber_rename {m k} (w f r : Fin m) (s : Fin m → Fin k) : (encodingFiber w f r).rename s = encodingFiber (s w) (s f) (s r) := by
  simp only [encodingFiber, Formula.rename, encoding_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem roundTrip_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (roundTrip w n).rename s = roundTrip (s w) (s n) := by
  simp only [roundTrip, roundTripBody, Formula.rename, hasLength_rename, fields_rename, encoding_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w f r a : Fin m) (ha : Derives Γ (encoding w f r a))
    (hu : Derives Γ (.all ((encoding w.castSucc f.castSucc r.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc)))) :
    Derives Γ (encodingFiber w f r) := by
  apply Derives.exI a
  simp only [Formula.instantiate, Formula.rename, encoding_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ha hu

theorem intro_roundTrip {m} {Γ : Context m} (w n l f a : Fin m)
    (hl : Derives Γ (hasLength w n l)) (hf : Derives Γ (fields w n l f))
    (ha : Derives Γ (encoding w f l a)) (he : Derives Γ (.equal a n)) : Derives Γ (roundTrip w n) := by
  apply Derives.exI l
  apply Derives.exI f
  apply Derives.exI a
  simp only [roundTripBody, Formula.instantiate, Formula.rename, hasLength_rename, fields_rename, encoding_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI (.conjI hl hf) ha) he
end PPAC.Migration.Internal.StructuralListRoundTripSyntax

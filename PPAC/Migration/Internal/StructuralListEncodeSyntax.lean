import PPAC.Migration.Internal.StructuralListSuffixInduction

/-! 任意内部完整序列的实际逆编码合同，保留原HasLength与完整Fields图。 -/
namespace PPAC.Migration.Internal.StructuralListEncodeSyntax
open Source SourceAlgebra SourceLogic GraphSyntax StructuralListLengthSyntax StructuralListFieldSyntax StructuralListFieldGraphSyntax

def reading {m} (w f l n : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).imp
    ((field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def encoding {m} (w f l n : Fin m) : Formula m := ((Formula.mem n w).conj (hasLength w n l)).conj (fields w n l f)

def existsEncoding {m} (w f l : Fin m) : Formula m := .ex (encoding w.castSucc f.castSucc l.castSucc (Fin.last m))

theorem reading_rename {m k} (w f l n : Fin m) (s : Fin m → Fin k) : (reading w f l n).rename s = reading (s w) (s f) (s l) (s n) := by
  simp only [reading, Formula.rename, Formula.iff, field_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem encoding_rename {m k} (w f l n : Fin m) (s : Fin m → Fin k) : (encoding w f l n).rename s = encoding (s w) (s f) (s l) (s n) := by
  simp only [encoding, Formula.rename, hasLength_rename, fields_rename]

theorem existsEncoding_rename {m k} (w f l : Fin m) (s : Fin m → Fin k) : (existsEncoding w f l).rename s = existsEncoding (s w) (s f) (s l) := by
  simp only [existsEncoding, Formula.rename, encoding_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem reading_at {m} {Γ : Context m} (w f l n i y : Fin m) (hr : Derives Γ (reading w f l n))
    (hi : Derives Γ (.mem i l)) : Derives Γ ((field w n i y).iff (edge f i y)) := by
  have h : Derives Γ ((Formula.mem i l).imp ((field w n i y).iff (edge f i y))) := by
    simpa only [reading, Formula.instantiate, Formula.rename, Formula.iff, field_rename, edge_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hr)
  exact .impE h hi

theorem intro_encoding {m} {Γ : Context m} (w f l n : Fin m) (hn : Derives Γ (.mem n w))
    (hl : Derives Γ (hasLength w n l)) (hf : Derives Γ (fields w n l f)) : Derives Γ (existsEncoding w f l) := by
  apply Derives.exI n
  simp only [Formula.instantiate, encoding_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hn hl) hf
end PPAC.Migration.Internal.StructuralListEncodeSyntax

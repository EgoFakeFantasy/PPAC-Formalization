import PPAC.Migration.Internal.SyntaxFreeSubstFields
import PPAC.Migration.Internal.SyntaxRenameTerm

/-! 混合替换的实际完整项像表；两类源变量都可取任意合法目标bound/free项。 -/
namespace PPAC.Migration.Internal.SyntaxTermImageSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxTermSyntax SequenceSyntax

def values {m} (w f c d : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)))))

def imageMap {m} (w f a c d : Fin m) : Formula m := (Formula.mem a w).conj
  ((contexts w c d).conj ((sequence f a w).conj (values w f c d)))

def maps {m} (w r s a b c d : Fin m) : Formula m :=
  (imageMap w r a c d).conj (imageMap w s b c d)

theorem values_rename {m k} (w f c d : Fin m) (ρ : Fin m → Fin k) :
    (values w f c d).rename ρ = values (ρ w) (ρ f) (ρ c) (ρ d) := by
  simp only [values, Formula.rename, edge_rename, term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem imageMap_rename {m k} (w f a c d : Fin m) (ρ : Fin m → Fin k) :
    (imageMap w f a c d).rename ρ = imageMap (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) := by
  simp only [imageMap, Formula.rename, contexts_rename, sequence_rename, values_rename]

theorem maps_rename {m k} (w r s a b c d : Fin m) (ρ : Fin m → Fin k) :
    (maps w r s a b c d).rename ρ = maps (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [maps, Formula.rename, imageMap_rename]

theorem values_at {m} {Γ : Context m} (w f c d i q : Fin m) (hv : Derives Γ (values w f c d)) :
    Derives Γ ((edge f i q).imp (term w c d q)) :=
  SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, term_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE i hv))

theorem image_function {m} {Γ : Context m} (w f a c d : Fin m) (hm : Derives Γ (imageMap w f a c d)) :
    Derives Γ (functionOn f a) := .conjL (.conjL (.conjR (.conjR hm)))

theorem image_sequence {m} {Γ : Context m} (w f a c d : Fin m) (hm : Derives Γ (imageMap w f a c d)) :
    Derives Γ (sequence f a w) := .conjL (.conjR (.conjR hm))

theorem image_type {m} {Γ : Context m} (w f a c d i q : Fin m)
    (hm : Derives Γ (imageMap w f a c d)) (he : Derives Γ (edge f i q)) : Derives Γ (term w c d q) :=
  .impE (values_at w f c d i q (.conjR (.conjR (.conjR hm)))) he

theorem image_natural {m} {Γ : Context m} (w f a c d i q : Fin m)
    (hm : Derives Γ (imageMap w f a c d)) (he : Derives Γ (edge f i q)) : Derives Γ (.mem q w) :=
  .impE (bounded_at f w i q (.conjR (image_sequence w f a c d hm))) he

theorem source_contexts {m} {Γ : Context m} (w r s a b c d : Fin m) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (contexts w a b) := .conjI (.conjL (.conjL hm)) (.conjL (.conjR hm))

theorem target_contexts {m} {Γ : Context m} (w r s a b c d : Fin m) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (contexts w c d) := .conjL (.conjR (.conjL hm))

theorem selected {m} {Γ : Context m} (bound : Bool) (w r s a b c d : Fin m)
    (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ (imageMap w (SyntaxIndexMapSyntax.selectMap bound r s) (limit bound a b) c d) := by
  cases bound
  · exact .conjR hm
  · exact .conjL hm

end PPAC.Migration.Internal.SyntaxTermImageSyntax

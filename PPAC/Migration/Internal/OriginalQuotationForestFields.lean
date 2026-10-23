import PPAC.Migration.Internal.OriginalQuotationFieldSyntax

/-! 给定实际子quotation码时，原森林quotation与完整有限字段编码精确等价。 -/
namespace PPAC.Migration.Internal.OriginalQuotationForestFields
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalQuotationFieldSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forest_of_fields {m} {Γ : Context m} (children : List Tree) (w p : Fin m) (xs : Fin children.length → Fin m)
    (hf : Derives Γ (fields children w xs)) (hp : Derives Γ (SyntaxForestSyntax.forest children.length w xs p)) :
    Derives Γ (forest children w p) := by
  cases children with
  | nil => exact of_eq (by simp only [forest, List.length_nil, SyntaxForestSyntax.forest]) hp
  | cons head tail =>
    let C := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((SyntaxForestSyntax.forest tail.length w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj
        (StructuralListSyntax.consCode w.castSucc (xs 0).castSucc (Fin.last m) p.castSucc))
    let Δ := Context.add C (Context.image Formula.raise Γ)
    apply SyntaxForestSyntax.eliminate_cons tail.length w xs p _ hp
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hf1 : Derives Δ (fields (head :: tail) w.castSucc (fun i => (xs i).castSucc)) :=
      of_eq (by simp only [Formula.raise, fields_rename]) (under hf C)
    have ht := forest_of_fields tail w.castSucc (Fin.last m) (fun i => (xs i.succ).castSucc) (.conjR hf1) (.conjL (.conjR hC))
    have ho := OriginalTreeQuotationSyntax.intro_cons head tail w.castSucc p.castSucc (xs 0).castSucc (Fin.last m) (.conjL hf1) ht (.conjR (.conjR hC))
    exact of_eq (forest_rename (head :: tail) w p Fin.castSucc).symm ho
termination_by children.length

theorem fields_output_subst {m} {Γ : Context m} (k : Nat) (w p q : Fin m) (xs : Fin k → Fin m)
    (he : Derives Γ (.equal p q)) (hp : Derives Γ (SyntaxForestSyntax.forest k w xs p)) :
    Derives Γ (SyntaxForestSyntax.forest k w xs q) := by
  have hi : Derives Γ ((SyntaxForestSyntax.forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).instantiate p) :=
    of_eq (by simp only [Formula.instantiate, SyntaxForestSyntax.forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp
  have ho := Derives.eqSubst (SyntaxForestSyntax.forest k w.castSucc (fun i => (xs i).castSucc) (Fin.last m)) he hi
  exact of_eq (by simp only [Formula.instantiate, SyntaxForestSyntax.forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho

theorem forest_to_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (children : List Tree) (w p : Fin m)
    (xs : Fin children.length → Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (fields children w xs))
    (hp : Derives Γ (forest children w p)) : Derives Γ (SyntaxForestSyntax.forest children.length w xs p) := by
  have hi := natural_fields hZ children w xs hw hf
  have he := SyntaxForests.exists_forest hZ children.length w xs hw hi
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest children.length w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hf1 : Derives Δ (fields children w.castSucc (fun i => (xs i).castSucc)) := of_eq (fields_rename children w xs Fin.castSucc) (under hf P)
  have hp1 : Derives Δ (forest children w.castSucc p.castSucc) := of_eq (forest_rename children w p Fin.castSucc) (under hp P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hQ := forest_of_fields children w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hf1 (.conjR hP)
  have heq := OriginalTreeQuotationUnique.forest_unique hZ1 children w.castSucc (Fin.last m) p.castSucc hw1 hQ hp1
  have ho := fields_output_subst children.length w.castSucc (Fin.last m) p.castSucc (fun i => (xs i).castSucc) heq (.conjR hP)
  exact of_eq (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename]) ho

theorem forest_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (children : List Tree) (w p : Fin m)
    (xs : Fin children.length → Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (fields children w xs)) :
    Derives Γ ((forest children w p).iff (SyntaxForestSyntax.forest children.length w xs p)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forest_to_fields (ZFContext.add hZ _) children w p xs (add hw _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact forest_of_fields children w p xs (add hf _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalQuotationForestFields

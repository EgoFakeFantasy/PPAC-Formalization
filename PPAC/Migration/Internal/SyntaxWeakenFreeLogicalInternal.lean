import PPAC.Migration.Internal.SyntaxWeakenFreeLogical

/-! 弱化逻辑构造律的全部映射码见证在对象存在量词内取得及消去。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeLogicalInternal
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxWeakenFreeSyntax (weakened weakened_rename)
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeShiftSyntax (shiftCode shiftCode_rename)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename quantifierTag)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def codeBody {m} (w a b B : Fin m) : Formula (m+2) :=
  (identityCode w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc).conj
    (shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)))

def actualCodes {m} (w a b B : Fin m) : Formula m := .ex (.ex (codeBody w a b B))

theorem actualCodes_rename {m k} (w a b B : Fin m) (ρ : Fin m → Fin k) :
    (actualCodes w a b B).rename ρ = actualCodes (ρ w) (ρ a) (ρ b) (ρ B) := by
  simp only [actualCodes, codeBody, Formula.rename, identityCode_rename, shiftCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actual_codes_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hB : Derives Γ (successor B b)) : Derives Γ (actualCodes w a b B) := by
  let R := identityCode w.castSucc a.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxIdentityCode.exists_code hZ w a hw ha)
  have hs : Derives Ξ (SyntaxFreeShiftSyntax.existsCode w.castSucc b.castSucc B.castSucc) :=
    of_eq (SyntaxFreeShiftSyntax.existsCode_rename w b B Fin.castSucc)
      (under (SyntaxFreeShiftCode.exists_code hZ w b B hw hb hB) R)
  let S := shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) hs
  have hr : Derives Ξ R := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, identityCode_rename]) (under hr S)
  have hs2 : Derives Δ S := .hyp (Or.inl rfl)
  have ho : Derives Δ (actualCodes w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simp only [codeBody, Formula.instantiate, Formula.rename, identityCode_rename, shiftCode_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hr2 hs2
  exact of_eq (by simp only [Formula.raise, actualCodes_rename]) ho

theorem actual_codes_elim {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B : Fin m) (P : Formula m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hB : Derives Γ (successor B b))
    (hc : Derives (Context.add (codeBody w a b B)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) P.raise.raise) : Derives Γ P :=
  SyntaxRenameBinders.eliminate_2 (codeBody w a b B) P
    (actual_codes_exists hZ w a b B hw ha hb hB) hc

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q x X : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b))
    (hn : Derives Γ (singleCode 4 w x n)) (hq : Derives Γ (singleCode 4 w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w a b B x X)) := by
  let C := codeBody w a b B
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w a b B _ hw ha hb hB
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hn2 : Derives Δ (singleCode 4 w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (singleCode 4 w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have ho := SyntaxWeakenFreeLogical.negation_iff hZ2
    w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hC) (.conjR hC) hn2 hq2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, weakened_rename]) ho

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w a b B n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b))
    (hn : Derives Γ (binaryCode kind w x y n)) (hq : Derives Γ (binaryCode kind w X Y q)) :
    Derives Γ ((weakened w a b B n q).iff ((weakened w a b B x X).conj (weakened w a b B y Y))) := by
  let C := codeBody w a b B
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w a b B _ hw ha hb hB
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hn2 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have ho := SyntaxWeakenFreeLogical.binary_iff hZ2 kind
    w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hC) (.conjR hC) hn2 hq2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, weakened_rename]) ho

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w a b B n q x X u : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b))
    (hu : Derives Γ (successor u a))
    (hn : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hq : Derives Γ (singleCode (quantifierTag universal) w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w u b B x X)) := by
  let C := codeBody w a b B
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w a b B _ hw ha hb hB
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hu2 : Derives Δ (successor u.castSucc.castSucc a.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hu C)
  have hn2 : Derives Δ (singleCode (quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (singleCode (quantifierTag universal) w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have huN := OmegaStructureAlgebra.successor_member w.castSucc.castSucc u.castSucc.castSucc a.castSucc.castSucc
    (ZFContext.arithmetic hZ2).base.extensionality hw2 (SyntaxRenameBinders.under_2 ha C) hu2
  let L := identityCode w.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add L (Context.image Formula.raise Δ)
  apply Derives.exE (p := L) (SyntaxIdentityCode.exists_code hZ2 w.castSucc.castSucc u.castSucc.castSucc hw2 huN)
  have hZ3 := ZFContext.under hZ2 L
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) :=
    of_eq (omega_rename _ Fin.castSucc) (under hw2 L)
  have hu3 : Derives Ξ (successor u.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) :=
    of_eq (successor_rename _ _ Fin.castSucc) (under hu2 L)
  have hn3 : Derives Ξ (singleCode (quantifierTag universal) w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) :=
    of_eq (singleCode_rename _ _ _ _ Fin.castSucc) (under hn2 L)
  have hq3 : Derives Ξ (singleCode (quantifierTag universal) w.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc) :=
    of_eq (singleCode_rename _ _ _ _ Fin.castSucc) (under hq2 L)
  have hr3 : Derives Ξ (identityCode w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) :=
    of_eq (identityCode_rename _ _ _ Fin.castSucc) (under (.conjL hC) L)
  have hs3 : Derives Ξ (shiftCode w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (shiftCode_rename _ _ _ _ Fin.castSucc) (under (.conjR hC) L)
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have ho := SyntaxWeakenFreeLogical.quantified_iff hZ3 universal
    w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc
    n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc u.castSucc.castSucc.castSucc (Fin.last (m+2))
    hw3 hr3 hs3 hu3 hL hn3 hq3
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, weakened_rename]) ho

end PPAC.Migration.Internal.SyntaxWeakenFreeLogicalInternal

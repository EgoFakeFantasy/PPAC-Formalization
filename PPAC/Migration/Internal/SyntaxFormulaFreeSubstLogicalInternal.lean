import PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogical

/-! 原项列表参数的逻辑替换律：全部恒等/转换码见证在对象量词内取得并消去。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogicalInternal
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxFormulaFreeSubstSyntax (substituted substituted_rename)
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeSubstSyntax (codeConversion codeConversion_rename termList termList_rename)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename quantifierTag)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def codeBody {m} (w b a c L : Fin m) : Formula (m+2) :=
  (identityCode w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
    (codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1)))

def actualCodes {m} (w b a c L : Fin m) : Formula m := .ex (.ex (codeBody w b a c L))

theorem actualCodes_rename {m k} (w b a c L : Fin m) (ρ : Fin m → Fin k) :
    (actualCodes w b a c L).rename ρ = actualCodes (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) := by
  simp only [actualCodes, codeBody, Formula.rename, identityCode_rename, codeConversion_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem actual_codes_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hL : Derives Γ (termList w a c L)) :
    Derives Γ (actualCodes w b a c L) := by
  let R := identityCode w.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxIdentityCode.exists_code hZ w b hw hb)
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 : Derives Ξ (termList w.castSucc a.castSucc c.castSucc L.castSucc) := of_eq (termList_rename w a c L Fin.castSucc) (under hL R)
  let S := codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) (SyntaxFreeSubstCode.from_list (ZFContext.under hZ R) _ _ _ _ hw1 hl1)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, identityCode_rename]) (under hR S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have ho : Derives Δ (actualCodes w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc
    apply Derives.exI (Fin.last (m+1))
    simp only [codeBody, Formula.instantiate, Formula.rename, identityCode_rename, codeConversion_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hr2 hS
  exact of_eq (by simp only [Formula.raise, actualCodes_rename]) ho

theorem actual_codes_elim {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L : Fin m) (P : Formula m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hL : Derives Γ (termList w a c L))
    (hc : Derives (Context.add (codeBody w b a c L)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) P.raise.raise) : Derives Γ P :=
  SyntaxRenameBinders.eliminate_2 (codeBody w b a c L) P (actual_codes_exists hZ w b a c L hw hb hL) hc

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q x X : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (.mem b w)) (hL : Derives Γ (termList w a c L))
    (hn : Derives Γ (singleCode 4 w x n)) (hq : Derives Γ (singleCode 4 w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w b a c L x X)) := by
  let C := codeBody w b a c L
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w b a c L _ hw hb hL
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hn2 : Derives Δ (singleCode 4 w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (singleCode 4 w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have ho := SyntaxFormulaFreeSubstLogical.negation_iff hZ2
    w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hC) (.conjR hC) hn2 hq2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename]) ho

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w b a c L n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (.mem b w)) (hL : Derives Γ (termList w a c L))
    (hn : Derives Γ (binaryCode kind w x y n)) (hq : Derives Γ (binaryCode kind w X Y q)) :
    Derives Γ ((substituted w b a c L n q).iff ((substituted w b a c L x X).conj (substituted w b a c L y Y))) := by
  let C := codeBody w b a c L
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w b a c L _ hw hb hL
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hn2 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have ho := SyntaxFormulaFreeSubstLogical.binary_iff hZ2 kind
    w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjL hC) (.conjR hC) hn2 hq2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename]) ho

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w b a c L n q x X u : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (.mem b w)) (hL : Derives Γ (termList w a c L))
    (hu : Derives Γ (successor u b))
    (hn : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hq : Derives Γ (singleCode (quantifierTag universal) w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w u a c L x X)) := by
  let C := codeBody w b a c L
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply actual_codes_elim hZ w b a c L _ hw hb hL
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hu2 : Derives Δ (successor u.castSucc.castSucc b.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hu C)
  have hn2 : Derives Δ (singleCode (quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hn C)
  have hq2 : Derives Δ (singleCode (quantifierTag universal) w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (SyntaxRenameBinders.under_2 hq C)
  have huN := OmegaStructureAlgebra.successor_member w.castSucc.castSucc u.castSucc.castSucc b.castSucc.castSucc
    (ZFContext.arithmetic hZ2).base.extensionality hw2 (SyntaxRenameBinders.under_2 hb C) hu2
  let K := identityCode w.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add K (Context.image Formula.raise Δ)
  apply Derives.exE (p := K) (SyntaxIdentityCode.exists_code hZ2 w.castSucc.castSucc u.castSucc.castSucc hw2 huN)
  have hZ3 := ZFContext.under hZ2 K
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) :=
    of_eq (omega_rename _ Fin.castSucc) (under hw2 K)
  have hu3 : Derives Ξ (successor u.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc) :=
    of_eq (successor_rename _ _ Fin.castSucc) (under hu2 K)
  have hn3 : Derives Ξ (singleCode (quantifierTag universal) w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) :=
    of_eq (singleCode_rename _ _ _ _ Fin.castSucc) (under hn2 K)
  have hq3 : Derives Ξ (singleCode (quantifierTag universal) w.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc) :=
    of_eq (singleCode_rename _ _ _ _ Fin.castSucc) (under hq2 K)
  have hr3 : Derives Ξ (identityCode w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) :=
    of_eq (identityCode_rename _ _ _ Fin.castSucc) (under (.conjL hC) K)
  have hs3 : Derives Ξ (codeConversion w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (codeConversion_rename _ _ _ _ _ Fin.castSucc) (under (.conjR hC) K)
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaFreeSubstLogical.quantified_iff hZ3 universal
    w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc
    n.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc u.castSucc.castSucc.castSucc (Fin.last (m+2))
    hw3 hr3 hs3 hu3 hK hn3 hq3
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename]) ho

end PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogicalInternal

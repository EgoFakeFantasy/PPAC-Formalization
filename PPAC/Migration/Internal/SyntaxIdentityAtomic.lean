import PPAC.Migration.Internal.SyntaxRenameIdentitySyntax

/-! 四类原子在实际对角图及其自然码下自重命名；正式消去原子字段。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameIdentitySyntax
open SyntaxMapCodeSyntax SyntaxRenameTermIdentity SyntaxAtomSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b b S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (hc : Derives Γ (equality w a b n)) : Derives Γ (self w R S a b n) := by
  let B := equalBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply SyntaxAtomLogic.eliminate_equality w a b n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 hr B)
  have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 hs B)
  have dr2 : Derives Δ (diagonal r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (under_2 dr B)
  have ds2 : Derives Δ (diagonal s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (under_2 ds B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermIdentity.reflexive (zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjI (.conjR hr2) (.conjR hs2)) dr2 ds2 (.conjL (.conjL hB))
  have hy := SyntaxRenameTermIdentity.reflexive (zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjI (.conjR hr2) (.conjR hs2)) dr2 ds2 (.conjR (.conjL hB))
  have ho := Derives.impE (.conjR (SyntaxRenameKnownFields.equality_iff (zf_under_2 hZ B) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (Fin.last m).castSucc (Fin.last (m+1)) hw2 hr2 hs2 (.conjR hB) (.conjR hB))) (.conjI hx hy)
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b b S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (hc : Derives Γ (membership w a b n)) : Derives Γ (self w R S a b n) := by
  let B := memberBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply SyntaxAtomLogic.eliminate_member w a b n _ hc
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
  have hr3 : Derives Δ (encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three hr B)
  have hs3 : Derives Δ (encoded w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three hs B)
  have dr3 : Derives Δ (diagonal r.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxAtomLogic.under_three dr B)
  have ds3 : Derives Δ (diagonal s.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxAtomLogic.under_three ds B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermIdentity.reflexive (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (.conjI (.conjR hr3) (.conjR hs3)) dr3 ds3 (.conjL (.conjR (.conjL hB)))
  have hy := SyntaxRenameTermIdentity.reflexive (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3 (.conjI (.conjR hr3) (.conjR hs3)) dr3 ds3 (.conjR (.conjR (.conjL hB)))
  have ho := Derives.impE (.conjR (SyntaxRenameKnownFields.membership_iff (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hr3 hs3 (.conjR hB) (.conjR hB))) (.conjI (.conjL (.conjL hB)) (.conjI (.eqRefl (Fin.last m).castSucc.castSucc) (.conjI hx hy)))
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w R S r s a b n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b b S))
    (hc : Derives Γ (SyntaxAtomSyntax.nullary truth w a b n)) : Derives Γ (self w R S a b n) :=
  .impE (.conjR (SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s a b a b n n hw hr hs (.conjR hc))) (.eqRefl n)

theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b b S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (ha : Derives Γ (atomic w a b n)) : Derives Γ (self w R S a b n) := by
  apply Derives.disjE ha
  · let C := (SyntaxAtomSyntax.nullary false w a b n).disj (SyntaxAtomSyntax.nullary true w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) false w R S r s a b n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (.hyp (Or.inl rfl))
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) true w R S r s a b n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (.hyp (Or.inl rfl))
  · let C := (SyntaxAtomSyntax.membership w a b n).disj (SyntaxAtomSyntax.equality w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact membership (ZFContext.add (ZFContext.add hZ C) _) w R S r s a b n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (add (add dr C) _) (add (add ds C) _) (.hyp (Or.inl rfl))
    · exact equality (ZFContext.add (ZFContext.add hZ C) _) w R S r s a b n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (add (add dr C) _) (add (add ds C) _) (.hyp (Or.inl rfl))

theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a R))
    (hs : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b S)) (ha : Derives Γ (atomic w a b n)) : Derives Γ (self w R S a b n) := by
  let G := (encoded w.castSucc (Fin.last m) a.castSucc a.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hr
  have hs1 : Derives Ξ (SyntaxIdentityMapSyntax.identityCode w.castSucc b.castSucc S.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w b S Fin.castSucc) (under hs G)
  let H := (encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc).conj (diagonal (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have g2 : Derives Δ ((encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc).conj (diagonal (Fin.last m).castSucc)) := of_eq (by simp only [G, Formula.raise, Formula.rename, encoded_rename, diagonal_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have ha2 : Derives Δ (atomic w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, atomic_rename]) (under (under ha G) H)
  have ho := at_graphs (ZFContext.under (ZFContext.under hZ G) H) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL g2) (.conjL hH) (.conjR g2) (.conjR hH) ha2
  exact of_eq (by simp only [Formula.raise, self_rename]) ho
end PPAC.Migration.Internal.SyntaxIdentityAtomic

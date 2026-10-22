import PPAC.Migration.Internal.SyntaxComposeLiftGraph

/-! 三组真实自然码提升与实际复合相容，所有原图和提升图均在对象存在量词内取得。 -/
namespace PPAC.Migration.Internal.SyntaxComposeLiftCode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMapCodeSyntax SyntaxComposeCodeSyntax SyntaxRenameQuerySyntax
open SyntaxIndexLiftSyntax (lifted lifted_rename)
open SyntaxMapLiftSyntax (codedLift codedLift_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_sources {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t g a c e R T K A C E Lr Lt Lk : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxComposeSyntax.composed w r t a c e g))
    (er : Derives Γ (encoded w r a c R)) (et : Derives Γ (encoded w t c e T)) (eg : Derives Γ (encoded w g a e K))
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T C E Lt))
    (hk : Derives Γ (codedLift w a e K A E Lk)) : Derives Γ (coded w A C E Lr Lt Lk) := by
  let P := (lifted w.castSucc r.castSucc a.castSucc c.castSucc A.castSucc C.castSucc (Fin.last m)).conj (encoded w.castSucc (Fin.last m) A.castSucc C.castSucc Lr.castSucc)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxMapLift.at_source hZ w r a c R A C Lr er hr)
  have hZ1 := ZFContext.under hZ P
  have et1 : Derives Ξ (encoded w.castSucc t.castSucc c.castSucc e.castSucc T.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under et P)
  have ht1 : Derives Ξ (codedLift w.castSucc c.castSucc e.castSucc T.castSucc C.castSucc E.castSucc Lt.castSucc) := of_eq (codedLift_rename _ _ _ _ _ _ _ Fin.castSucc) (under ht P)
  let Q := (lifted w.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc C.castSucc.castSucc E.castSucc.castSucc (Fin.last (m+1))).conj (encoded w.castSucc.castSucc (Fin.last (m+1)) C.castSucc.castSucc E.castSucc.castSucc Lt.castSucc.castSucc)
  let Ψ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) (SyntaxMapLift.at_source hZ1 _ _ _ _ _ _ _ _ et1 ht1)
  have hZ2 := ZFContext.under hZ1 Q
  have eg2 : Derives Ψ (encoded w.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc e.castSucc.castSucc K.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under (under eg P) Q)
  have hk2 : Derives Ψ (codedLift w.castSucc.castSucc a.castSucc.castSucc e.castSucc.castSucc K.castSucc.castSucc A.castSucc.castSucc E.castSucc.castSucc Lk.castSucc.castSucc) := of_eq (by simp only [Formula.raise, codedLift_rename]) (under (under hk P) Q)
  let Z := (lifted w.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc (Fin.last (m+2))).conj (encoded w.castSucc.castSucc.castSucc (Fin.last (m+2)) A.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lk.castSucc.castSucc.castSucc)
  let Δ := Context.add Z (Context.image Formula.raise Ψ)
  apply Derives.exE (p := Z) (SyntaxMapLift.at_source hZ2 _ _ _ _ _ _ _ _ eg2 hk2)
  have hZ3 := ZFContext.under hZ2 Z
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under (under hw P) Q) Z)
  have hc3 : Derives Δ (SyntaxComposeSyntax.composed w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxComposeSyntax.composed_rename]) (under (under (under hc P) Q) Z)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hp3 : Derives Δ ((lifted w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj (encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc Lr.castSucc.castSucc.castSucc)) := of_eq (by simp only [P, Formula.raise, Formula.rename, lifted_rename, encoded_rename]) (under (under hP Q) Z)
  have hQ : Derives Ψ Q := .hyp (Or.inl rfl)
  have hq3 : Derives Δ ((lifted w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj (encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lt.castSucc.castSucc.castSucc)) := of_eq (by simp only [Q, Formula.raise, Formula.rename, lifted_rename, encoded_rename]) (under hQ Z)
  have hOut : Derives Δ Z := .hyp (Or.inl rfl)
  have hcomp := SyntaxComposeLiftGraph.composition hZ3 w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hc3 (.conjL hp3) (.conjL hq3) (.conjL hOut)
  have ho := intro_code w.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lr.castSucc.castSucc.castSucc Lt.castSucc.castSucc.castSucc Lk.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (.conjR hp3) (.conjR hq3) hcomp (.conjR hOut)
  exact of_eq (by simp only [Formula.raise, coded_rename]) ho

theorem composition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T K A C E Lr Lt Lk : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (coded w a c e R T K))
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T C E Lt))
    (hk : Derives Γ (codedLift w a e K A E Lk)) : Derives Γ (coded w A C E Lr Lt Lk) := by
  let B := body w a c e R T K
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_code w a c e R T K _ hc
  have hZ3 := SyntaxAtomLogic.zf_under_three hZ B
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
  have hr3 : Derives Δ (codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc Lr.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, codedLift_rename]) (SyntaxAtomLogic.under_three hr B)
  have ht3 : Derives Δ (codedLift w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lt.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, codedLift_rename]) (SyntaxAtomLogic.under_three ht B)
  have hk3 : Derives Δ (codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lk.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, codedLift_rename]) (SyntaxAtomLogic.under_three hk B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_sources hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc E.castSucc.castSucc.castSucc Lr.castSucc.castSucc.castSucc Lt.castSucc.castSucc.castSucc Lk.castSucc.castSucc.castSucc hw3 (.conjL (.conjR (.conjR hB))) (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR (.conjR hB))) hr3 ht3 hk3
  exact of_eq (by simp only [Formula.raise, coded_rename]) ho
end PPAC.Migration.Internal.SyntaxComposeLiftCode

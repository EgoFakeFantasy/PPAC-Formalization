import PPAC.Migration.ForcingBinderFormula
import PPAC.Migration.Internal.SyntaxFreeShiftFiber

/-! Necessary source Global scope adapter: an actual diagonal index code
may embed one scope in another. Reuse the existing term identity, graph
decoding, binder lift and original Foundation/Separation proof pattern.
The old same-scope identity theorem and every original proof remain unchanged.
No new syntax operation, recursion or proof/induction backend. -/
namespace PPAC.Migration.ForcingScopeIdentity
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMapCodeSyntax SyntaxRenameTermIdentity SyntaxAtomSyntax SyntaxRenameBinders
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open FormulaCodeRecursiveSyntax SyntaxLogicalSyntax
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Same actual diagonal graph, with independently typed source/target scopes.
This does not require those scopes to be equal. -/
def diagonalCode {m} (w a c R : Fin m) : Formula m := .ex
  ((encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc).conj (diagonal (Fin.last m)))

theorem diagonalCode_rename {m l} (w a c R : Fin m) (ρ : Fin m → Fin l) :
    (diagonalCode w a c R).rename ρ = diagonalCode (ρ w) (ρ a) (ρ c) (ρ R) := by
  simp only [diagonalCode, Formula.rename, encoded_rename, diagonal_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem map_code {m} {Γ : Context m} (w a c R : Fin m) (hi : Derives Γ (diagonalCode w a c R)) :
    Derives Γ (mapCode w a c R) := by
  let E := (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (mapCode_rename w a c R Fin.castSucc).symm
    (SyntaxMapCodeSyntax.intro_code w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc (.conjL hE))

private theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c R r : Fin m)
    (hi : Derives Γ (diagonalCode w a c R)) (hr : Derives Γ (encoded w r a c R)) : Derives Γ (diagonal r) := by
  let E := (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr1 := of_eq (encoded_rename w r a c R Fin.castSucc) (under hr E)
  have he := SyntaxMapCode.unique_graph (ZFContext.under hZ E) w.castSucc (Fin.last m) r.castSucc a.castSucc c.castSucc R.castSucc (.conjL hE) hr1
  exact of_eq (diagonal_rename r Fin.castSucc).symm (SyntaxIdentityCode.diagonal_subst _ _ he (.conjR hE))

private theorem lift_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c R u v L : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (diagonalCode w a c R))
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c R u v L)) : Derives Γ (diagonalCode w u v L) := by
  let E := SyntaxMapLiftSyntax.body w a c R u v L
  let Δ := Context.add E (raisedContext 2 Γ)
  apply SyntaxMapLiftSyntax.eliminate_lift w a c R u v L _ hl
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi2 := of_eq (diagonalCode_rename w a c R (old 2)) (HornBinderRules.under_body 2 hi E)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hd := at_graph (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 a) (old 2 c) (old 2 R) (slot 2 0) hi2 (.conjL hE)
  have hg := SyntaxIdentityLift.graph_diagonal (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (slot 2 0) (old 2 a) (old 2 c) (old 2 u) (old 2 v) (slot 2 1) hw2 hd (.conjL (.conjR hE))
  have ho : Derives Δ (diagonalCode (old 2 w) (old 2 u) (old 2 v) (old 2 L)) := by
    apply Derives.exI (slot 2 1)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, encoded_rename, diagonal_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjR (.conjR hE)) hg)
  exact of_eq (by simp only [Formula.raise, diagonalCode_rename]; rfl) ho

private def self {m} (w R S a b c d n : Fin m) : Formula m :=
  SyntaxRenameJudgmentSyntax.renamed w R S a b c d n n

private theorem self_rename {m l} (w R S a b c d n : Fin m) (ρ : Fin m → Fin l) :
    (self w R S a b c d n).rename ρ = self (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) :=
  SyntaxRenameJudgmentSyntax.renamed_rename w R S a b c d n n ρ

namespace Atomic
private theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (hc : Derives Γ (equality w a b n)) : Derives Γ (self w R S a b c d n) := by
  let B := equalBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply SyntaxAtomLogic.eliminate_equality w a b n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 hr B)
  have hs2 : Derives Δ (encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (under_2 hs B)
  have dr2 : Derives Δ (diagonal r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (under_2 dr B)
  have ds2 : Derives Δ (diagonal s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (under_2 ds B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermIdentity.reflexive (zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjI (.conjR hr2) (.conjR hs2)) dr2 ds2 (.conjL (.conjL hB))
  have hy := SyntaxRenameTermIdentity.reflexive (zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjI (.conjR hr2) (.conjR hs2)) dr2 ds2 (.conjR (.conjL hB))
  have ho := Derives.impE (.conjR (SyntaxRenameKnownFields.equality_iff (zf_under_2 hZ B) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (Fin.last m).castSucc (Fin.last (m+1)) hw2 hr2 hs2 (.conjR hB) (.conjR hB))) (.conjI hx hy)
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

private theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (hc : Derives Γ (membership w a b n)) : Derives Γ (self w R S a b c d n) := by
  let B := memberBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply SyntaxAtomLogic.eliminate_member w a b n _ hc
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
  have hr3 : Derives Δ (encoded w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three hr B)
  have hs3 : Derives Δ (encoded w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, encoded_rename]) (SyntaxAtomLogic.under_three hs B)
  have dr3 : Derives Δ (diagonal r.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxAtomLogic.under_three dr B)
  have ds3 : Derives Δ (diagonal s.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonal_rename]) (SyntaxAtomLogic.under_three ds B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermIdentity.reflexive (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (.conjI (.conjR hr3) (.conjR hs3)) dr3 ds3 (.conjL (.conjR (.conjL hB)))
  have hy := SyntaxRenameTermIdentity.reflexive (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3 (.conjI (.conjR hr3) (.conjR hs3)) dr3 ds3 (.conjR (.conjR (.conjL hB)))
  have ho := Derives.impE (.conjR (SyntaxRenameKnownFields.membership_iff (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hr3 hs3 (.conjR hB) (.conjR hB))) (.conjI (.conjL (.conjL hB)) (.conjI (.eqRefl (Fin.last m).castSucc.castSucc) (.conjI hx hy)))
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

private theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w R S r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (SyntaxAtomSyntax.nullary truth w a b n)) : Derives Γ (self w R S a b c d n) :=
  .impE (.conjR (SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s a b c d n n hw hr hs (.conjR hc))) (.eqRefl n)

private theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (dr : Derives Γ (diagonal r)) (ds : Derives Γ (diagonal s))
    (ha : Derives Γ (atomic w a b n)) : Derives Γ (self w R S a b c d n) := by
  apply Derives.disjE ha
  · let C := (SyntaxAtomSyntax.nullary false w a b n).disj (SyntaxAtomSyntax.nullary true w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) false w R S r s a b c d n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (.hyp (Or.inl rfl))
    · exact nullary (ZFContext.add (ZFContext.add hZ C) _) true w R S r s a b c d n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (.hyp (Or.inl rfl))
  · let C := (SyntaxAtomSyntax.membership w a b n).disj (SyntaxAtomSyntax.equality w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact membership (ZFContext.add (ZFContext.add hZ C) _) w R S r s a b c d n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (add (add dr C) _) (add (add ds C) _) (.hyp (Or.inl rfl))
    · exact equality (ZFContext.add (ZFContext.add hZ C) _) w R S r s a b c d n (add (add hw C) _) (add (add hr C) _) (add (add hs C) _) (add (add dr C) _) (add (add ds C) _) (.hyp (Or.inl rfl))

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (diagonalCode w a c R))
    (hs : Derives Γ (diagonalCode w b d S)) (ha : Derives Γ (atomic w a b n)) : Derives Γ (self w R S a b c d n) := by
  let G := (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc).conj (diagonal (Fin.last m))
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hr
  have hs1 : Derives Ξ (diagonalCode w.castSucc b.castSucc d.castSucc S.castSucc) := of_eq (diagonalCode_rename w b d S Fin.castSucc) (under hs G)
  let H := (encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc).conj (diagonal (Fin.last (m+1)))
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have g2 : Derives Δ ((encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc).conj (diagonal (Fin.last m).castSucc)) := of_eq (by simp only [G, Formula.raise, Formula.rename, encoded_rename, diagonal_rename]) (under hG H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have ha2 : Derives Δ (atomic w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, atomic_rename]) (under (under ha G) H)
  have ho := at_graphs (ZFContext.under (ZFContext.under hZ G) H) w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL g2) (.conjL hH) (.conjR g2) (.conjR hH) ha2
  exact of_eq (by simp only [Formula.raise, self_rename]) ho

end Atomic
private def input {m} (w R S a b c d n : Fin m) : Formula m :=
  (formulaCode w n a b).conj ((diagonalCode w a c R).conj (diagonalCode w b d S))

private theorem input_rename {m l} (w R S a b c d n : Fin m) (ρ : Fin m → Fin l) :
    (input w R S a b c d n).rename ρ = input (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [input, Formula.rename, formulaCode_rename, diagonalCode_rename]

private def propertyBody {m} (w n : Fin m) : Formula (m+6) :=
  (input (old 6 w) (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 n)).imp
    (self (old 6 w) (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 n))
private def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 6 (propertyBody w n)
private theorem property_rename {m l} (w n : Fin m) (ρ : Fin m → Fin l) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, OriginalUniversalBlock.allMany_rename, propertyBody, Formula.rename, input_rename, self_rename, lift_old, lift_slot]

private def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))
private theorem earlier_rename {m l} (w n : Fin m) (ρ : Fin m → Fin l) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem property_at {m} {Γ : Context m} (w n R S a b c d : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ ((input w R S a b c d n).imp (self w R S a b c d n)) := by
  let values : Fin 6 → Fin m := Fin.cases R (Fin.cases S (Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))))
  exact of_eq (by simp only [propertyBody, Formula.rename, input_rename, self_rename, assign_old, assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 6 _ values hp)

private theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n))
    (hw : Derives Γ (.mem x w)) (hx : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hi : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x he)
  exact .impE hi (.conjI hw hx)

private theorem child {m} {Γ : Context m} (w n x R S a b c d : Fin m) (he : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x n)) (hc : Derives Γ (formulaCode w x a b))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S)) :
    Derives Γ (self w R S a b c d x) :=
  .impE (property_at w x R S a b c d (earlier_at w n x he (.conjL (FormulaCodeProperties.guards w x a b hc)) hx))
    (.conjI hc (.conjI hr hs))

private def qInput {m} (universal : Bool) (w R S a b c d n x : Fin m) : Formula m :=
  (omega w).conj ((earlier w n).conj ((diagonalCode w a c R).conj ((diagonalCode w b d S).conj
    ((singleCode (quantifierTag universal) w x n).conj ((Formula.mem x n).conj (advancedCode w x a b))))))

private theorem qInput_rename {m l} (universal : Bool) (w R S a b c d n x : Fin m) (ρ : Fin m → Fin l) :
    (qInput universal w R S a b c d n x).rename ρ =
      qInput universal (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ x) := by
  simp only [qInput, Formula.rename, omega_rename, earlier_rename, diagonalCode_rename, singleCode_rename, advancedCode_rename]

private theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w R S a b c d n x : Fin m) (hi : Derives Γ (qInput universal w R S a b c d n x)) :
    Derives Γ (self w R S a b c d n) := by
  let U := (successor (Fin.last m) a.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) b.castSucc)
  let Δ1 := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) (Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))
  have hU : Derives Δ1 U := .hyp (Or.inl rfl)
  have h1 := of_eq (qInput_rename universal w R S a b c d n x Fin.castSucc) (under hi U)
  have hZ1 := ZFContext.under hZ U
  have hw1 := Derives.conjL h1
  have hr1 := Derives.conjL (.conjR (.conjR h1))
  have hc1 := Derives.conjR (SyntaxMapCodeDecode.contexts w.castSucc a.castSucc c.castSucc R.castSucc
    (map_code w.castSucc a.castSucc c.castSucc R.castSucc hr1))
  have hv := Derives.impE (step_at w.castSucc c.castSucc (.conjL hw1)) hc1
  let V := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) c.castSucc.castSucc)
  let Δ2 := Context.add V (Context.image Formula.raise Δ1)
  apply Derives.exE (p := V) hv
  have hV : Derives Δ2 V := .hyp (Or.inl rfl)
  have h2 := of_eq (qInput_rename universal w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc x.castSucc Fin.castSucc) (under h1 V)
  have hU2 : Derives Δ2 ((successor (Fin.last m).castSucc (old 2 a)).conj
      (formulaCode (old 2 w) (old 2 x) (Fin.last m).castSucc (old 2 b))) :=
    of_eq (by simp only [U, Formula.raise, Formula.rename, successor_rename, formulaCode_rename]; rfl) (under hU V)
  have hZ2 := ZFContext.under hZ1 V
  have hw2 := Derives.conjL h2
  have hr2 := Derives.conjL (.conjR (.conjR h2))
  have hl := SyntaxMapLift.exists_code hZ2 (old 2 w) (old 2 a) (old 2 c) (old 2 R)
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (map_code _ _ _ _ hr2) (.conjL hU2) (.conjR hV)
  let L := SyntaxMapLiftSyntax.codedLift (old 3 w) (old 3 a) (old 3 c) (old 3 R)
    (old 2 (Fin.last m)) (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ3 := Context.add L (Context.image Formula.raise Δ2)
  apply Derives.exE (p := L) hl
  have hL : Derives Δ3 L := .hyp (Or.inl rfl)
  have h3 := of_eq (qInput_rename universal (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b)
    (old 2 c) (old 2 d) (old 2 n) (old 2 x) Fin.castSucc) (under h2 L)
  have hZ3 := ZFContext.under hZ2 L
  have hw3 := Derives.conjL h3
  have hr3 := Derives.conjL (.conjR (.conjR h3))
  have hs3 := Derives.conjL (.conjR (.conjR (.conjR h3)))
  have he3 := Derives.conjL (.conjR h3)
  have hCtor := Derives.conjL (.conjR (.conjR (.conjR (.conjR h3))))
  have hx3 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h3)))))
  have ht3 : Derives Δ3 (formulaCode (old 3 w) (old 3 x) (old 2 (Fin.last m)) (old 3 b)) :=
    of_eq (by simp only [formulaCode_rename]; rfl) (under (.conjR hU2) L)
  have hd := lift_code hZ3 (old 3 w) (old 3 a) (old 3 c) (old 3 R)
    (old 2 (Fin.last m)) (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hr3 hL
  have hb := child (old 3 w) (old 3 n) (old 3 x) (Fin.last (m+2)) (old 3 S)
    (old 2 (Fin.last m)) (old 3 b) (Fin.last (m+1)).castSucc (old 3 d) he3 hx3 ht3 hd hs3
  have ho := Derives.impE (.conjR (SyntaxRenameCodeFields.quantified_at_lift hZ3 universal
    (old 3 w) (old 3 R) (old 3 S) (old 3 a) (old 3 b) (old 3 c) (old 3 d)
    (old 3 n) (old 3 n) (old 3 x) (old 3 x) (old 2 (Fin.last m)) (Fin.last (m+1)).castSucc (Fin.last (m+2))
    hw3 (map_code _ _ _ _ hs3) hL hCtor hCtor)) hb
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]; rfl) ho

private theorem single_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S))
    (hc : Derives Γ (singleCode tag w x n)) (hx : Derives Γ (.mem x n))
    (ht : Derives Γ (stepCheck advance w x a b)) : Derives Γ (self w R S a b c d n) := by
  rcases valid with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .impE (.conjR (SyntaxRenameCodeFields.single_iff hZ 4 false (Or.inl ⟨rfl,rfl⟩)
      w R S a b c d n n x x hw (map_code _ _ _ _ hr) (map_code _ _ _ _ hs) hc hc))
      (child w n x R S a b c d he hx ht hr hs)
  · exact quantified hZ true w R S a b c d n x (.conjI hw (.conjI he (.conjI hr (.conjI hs (.conjI hc (.conjI hx ht))))))
  · exact quantified hZ false w R S a b c d n x (.conjI hw (.conjI he (.conjI hr (.conjI hs (.conjI hc (.conjI hx ht))))))

private theorem binary_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n x y : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S))
    (hc : Derives Γ (binaryCode kind w x y n)) (hx : Derives Γ (.mem x n)) (hy : Derives Γ (.mem y n))
    (ht : Derives Γ ((formulaCode w x a b).conj (formulaCode w y a b))) : Derives Γ (self w R S a b c d n) :=
  .impE (.conjR (SyntaxRenameCodeFields.binary_iff hZ kind w R S a b c d n n x y x y hw
    (map_code _ _ _ _ hr) (map_code _ _ _ _ hs) hc hc))
    (.conjI (child w n x R S a b c d he hx (.conjL ht) hr hs) (child w n y R S a b c d he hy (.conjR ht) hr hs))

private theorem single_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S))
    (hc : Derives Γ (singleCase tag advance w a b n)) : Derives Γ (self w R S a b c d n) := by
  let B := singleCaseBody tag advance w a b n
  let Δ := Context.add B (Context.image Formula.raise (Γ))
  apply eliminate_single tag advance w a b n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he B)
  have hr1 : Derives Δ (diagonalCode w.castSucc a.castSucc c.castSucc R.castSucc) := of_eq (by simp only [Formula.raise, diagonalCode_rename]) (under hr B)
  have hs1 : Derives Δ (diagonalCode w.castSucc b.castSucc d.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, diagonalCode_rename]) (under hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := single_step (ZFContext.under hZ B) tag advance valid w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 he1 hr1 hs1 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, self_rename]) ho

private theorem binary_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S))
    (hc : Derives Γ (binaryCase kind w a b n)) : Derives Γ (self w R S a b c d n) := by
  let B := binaryCaseBody kind w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_binary kind w a b n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 he B)
  have hr2 : Derives Δ (diagonalCode w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonalCode_rename]) (under_2 hr B)
  have hs2 : Derives Δ (diagonalCode w.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, diagonalCode_rename]) (under_2 hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := binary_step (zf_under_2 hZ B) kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 he2 hr2 hs2 (.conjL hB) (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, self_rename]) ho

private theorem from_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (diagonalCode w a c R)) (hs : Derives Γ (diagonalCode w b d S))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ (self w R S a b c d n) := by
  have hrule := FormulaCodeRecursive.recursive_iff hZ w n a b hw
  have hcases : Derives Γ ((allCases w n a b).imp (self w R S a b c d n)) := by
    apply FormulaCodeCaseLogic.all_imp w n a b (self w R S a b c d n)
    · apply Derives.impI
      exact Atomic.at_codes (ZFContext.add hZ _) w R S a b c d n (add hw _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl,rfl⟩) w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 0 w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 1 w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 2 w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 3 w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S a b c d n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
  exact .impE hcases (.conjR (.impE (.conjL hrule) hc))

/-- Six metadata coordinates are bound in the OBJECT formula. This reuses
the original finite binder block, Foundation/Separation and case proofs. -/
private theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := input (old 6 w) (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 n)
  let Δ := Context.add E (raisedContext 6 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw E)
  have he6 := of_eq (earlier_rename w n (old 6)) (HornBinderRules.under_body 6 he E)
  exact from_code (HornBinderRules.zf_body 6 hZ E) (old 6 w) (slot 6 0) (slot 6 1)
    (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 n) hw6 he6
    (.conjL (.conjR hE)) (.conjR (.conjR hE)) (.conjL hE)

open ReplacementPredicates (paramsUp)
private def matrix : Formula 2 := property (0 : Fin 1).castSucc (Fin.last 1)

private def curried {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

private theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem curried_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (curried w n).rename ρ = curried (ρ w) (ρ n) := by
  simp only [curried, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem earlier_of_curried {m} {Γ : Context m} (w n : Fin m) (hc : Derives Γ (curried w n)) : Derives Γ (earlier w n) := by
  apply Derives.allI
  apply Derives.impI
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hc1 : Derives Δ (curried w.castSucc n.castSucc) := of_eq (curried_rename w n Fin.castSucc) (under hc C)
  have hh : Derives Δ ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m)))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE (Fin.last m) hc1)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact .impE (.impE hh (.conjL hC)) (.conjR hC)

private theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := curried w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have he := earlier_of_curried w.castSucc (Fin.last m) (Derives.hyp (Or.inl rfl) : Derives Δ I)
  exact property_from_earlier hZ1 w.castSucc (Fin.last m) hw1 he

private theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp]) hh

private theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have hp : Derives Γ ((Formula.mem n w).imp (property w n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_properties hZ w hw))
  exact .impE hp hn


/-- Scope-polymorphic specialization of the existing diagonal identity
proof pattern. Every formula, six scope/map parameters and binder lift is
internal, including nonstandard. No supplied IH or expected output equality. -/
theorem reflexive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (diagonalCode w a c R))
    (hs : Derives Γ (diagonalCode w b d S)) (hc : Derives Γ (formulaCode w n a b)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n n) :=
  .impE (property_at w n R S a b c d (at_natural hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hc))))
    (.conjI hc (.conjI hr hs))

/-- Actual consumer: recover the SAME literal formula code at the target
scope from its original diagonal query, not by assuming type monotonicity. -/
theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (diagonalCode w a c R))
    (hs : Derives Γ (diagonalCode w b d S)) (hc : Derives Γ (formulaCode w n a b)) :
    Derives Γ (formulaCode w n c d) :=
  SyntaxRenameJudgment.target_type w R S a b c d n n (reflexive hZ w R S a b c d n hw hr hs hc)

private theorem empty_shift {m} {Γ : Context m} (w z A I : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w z A I)) :
    Derives Γ (diagonalCode w z A I) := by
  let E := (encoded w.castSucc (Fin.last m) z.castSucc A.castSucc I.castSucc).conj
    (SyntaxFreeShiftSyntax.shiftMap w.castSucc z.castSucc A.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hI
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hd : Derives Δ (diagonal (Fin.last m)) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let K := GraphSyntax.edge (old 2 (Fin.last m)) (slot 2 0) (slot 2 1)
    let Ξ := Context.add K (raisedContext 2 Δ)
    have hK : Derives Ξ K := .hyp (Or.inl rfl)
    have hm := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w.castSucc z.castSucc A.castSucc (Fin.last m) (old 2))
      (HornBinderRules.under_body 2 (.conjR hE) K)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
    have hz2 := of_eq (empty_rename z.castSucc (old 2)) (HornBinderRules.under_body 2 hz1 K)
    exact .botE (.impE (SyntaxFreeShiftFiber.empty_source (old 3 w) (old 3 z) (old 3 A)
      (old 2 (Fin.last m)) (slot 2 0) (slot 2 1) hm hz2) hK)
  have ho : Derives Δ (diagonalCode w.castSucc z.castSucc A.castSucc I.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, encoded_rename, diagonal_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hE) hd)
  exact of_eq (diagonalCode_rename w z A I Fin.castSucc).symm ho

/-- The actual empty-bound shift, original free identity, their actual
mixed conversion and SAME literal G query at promoted bound scope.
All four outputs are OBJECT witnesses in promoted. -/
def promotedData {m} (w z b A G : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftCode w z A (v 0)).conj
    ((SyntaxIdentityMapSyntax.identityCode w b (v 1)).conj
      ((IndexTermImageCodeSyntax.environment w (v 0) (v 1) (v 2) (v 3) z b A b).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w (v 2) (v 3) z b A b G G).conj (formulaCode w G A b))))

theorem promotedData_rename {m l} (w z b A G : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (promotedData w z b A G v).rename ρ = promotedData (ρ w) (ρ z) (ρ b) (ρ A) (ρ G) (fun i => ρ (v i)) := by
  simp only [promotedData, Formula.rename, SyntaxFreeShiftSyntax.shiftCode_rename,
    SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.environment_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename, formulaCode_rename]

private def promotedBody {m} (w z b A G : Fin m) : Formula (m+4) :=
  promotedData (old 4 w) (old 4 z) (old 4 b) (old 4 A) (old 4 G) (slot 4)

def promoted {m} (w z b A G : Fin m) : Formula m := existsMany 4 (promotedBody w z b A G)
theorem promoted_rename {m l} (w z b A G : Fin m) (ρ : Fin m → Fin l) :
    (promoted w z b A G).rename ρ = promoted (ρ w) (ρ z) (ρ b) (ρ A) (ρ G) := by
  simp only [promoted, existsMany_rename, promotedBody, promotedData_rename, lift_old, lift_slot]

/-- Actual closed-background consumer. Produce and discharge ALL FOUR
old index/mixed code witnesses internally; source G is any internal typed
code. Neither its promoted type nor its identity query is assumed. -/
theorem promote {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hG : Derives Γ (formulaCode w G z b)) :
    Derives Γ (promoted w z b A G) := by
  have hctx := Derives.conjR (FormulaCodeProperties.guards w G z b hG)
  let E0 := SyntaxFreeShiftSyntax.shiftCode w.castSucc z.castSucc A.castSucc (Fin.last m)
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (SyntaxFreeShiftCode.exists_code hZ w z A hw (.conjL hctx) hA)
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E0)
  have hb1 : Derives Δ1 (.mem b.castSucc w.castSucc) := under (.conjR hctx) E0
  let E1 := SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 b) (Fin.last (m+1))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) (SyntaxIdentityCode.exists_code hZ1 w.castSucc b.castSucc hw1 hb1)
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E1)
  have hz2 : Derives Δ2 (empty (old 2 z)) := of_eq
    (by simp only [Formula.raise, empty_rename]; rfl) (under (under hz E0) E1)
  have hG2 : Derives Δ2 (formulaCode (old 2 w) (old 2 G) (old 2 z) (old 2 b)) := of_eq
    (by simp only [Formula.raise, formulaCode_rename]; rfl) (under (under hG E0) E1)
  have hI2 : Derives Δ2 (SyntaxFreeShiftSyntax.shiftCode (old 2 w) (old 2 z) (old 2 A) (Fin.last m).castSucc) :=
    of_eq (by simp only [E0, Formula.raise, SyntaxFreeShiftSyntax.shiftCode_rename]; rfl) (under hE0 E1)
  have hr := empty_shift (old 2 w) (old 2 z) (old 2 A) (Fin.last m).castSucc hz2 hI2
  have hs : Derives Δ2 (diagonalCode (old 2 w) (old 2 b) (old 2 b) (Fin.last (m+1))) := hE1
  have hi := reflexive hZ2 (old 2 w) (Fin.last m).castSucc (Fin.last (m+1)) (old 2 z) (old 2 b) (old 2 A) (old 2 b) (old 2 G) hw2 hr hs hG2
  have he := IndexTermImageEnvironment.exists_environment hZ2 (old 2 w) (Fin.last m).castSucc (Fin.last (m+1))
    (old 2 z) (old 2 b) (old 2 A) (old 2 b) hw2 (map_code _ _ _ _ hr) (map_code _ _ _ _ hs)
  let E2 := IndexTermImageCodeSyntax.environment (old 4 w) (old 3 (Fin.last m)) (old 2 (Fin.last (m+1)))
    (slot 2 0) (slot 2 1) (old 4 z) (old 4 b) (old 4 A) (old 4 b)
  let Δ4 := Context.add E2 (raisedContext 2 Δ2)
  apply HornBinderRules.eliminate_many 2 E2 _ he
  have hE2 : Derives Δ4 E2 := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename (old 2 w) (old 2)) (HornBinderRules.under_body 2 hw2 E2)
  have hi4 : Derives Δ4 (SyntaxRenameJudgmentSyntax.renamed (old 4 w) (old 3 (Fin.last m)) (old 2 (Fin.last (m+1)))
      (old 4 z) (old 4 b) (old 4 A) (old 4 b) (old 4 G) (old 4 G)) :=
    of_eq (by simp only [SyntaxRenameJudgmentSyntax.renamed_rename]; rfl) (HornBinderRules.under_body 2 hi E2)
  have hm := IndexFormulaRenameInduction.forward (HornBinderRules.zf_body 2 hZ2 E2)
    (old 4 w) (old 3 (Fin.last m)) (old 2 (Fin.last (m+1))) (slot 2 0) (slot 2 1)
    (old 4 z) (old 4 b) (old 4 A) (old 4 b) (old 4 G) (old 4 G) hw4 hE2 hi4
  have ht := SyntaxMixedFormulaJudgment.target_type (old 4 w) (slot 2 0) (slot 2 1)
    (old 4 z) (old 4 b) (old 4 A) (old 4 b) (old 4 G) (old 4 G) hm
  have hI4 : Derives Δ4 (SyntaxFreeShiftSyntax.shiftCode (old 4 w) (old 4 z) (old 4 A) (old 3 (Fin.last m))) :=
    of_eq (by simp only [SyntaxFreeShiftSyntax.shiftCode_rename]; rfl) (HornBinderRules.under_body 2 hI2 E2)
  have hJ4 : Derives Δ4 (SyntaxIdentityMapSyntax.identityCode (old 4 w) (old 4 b) (old 2 (Fin.last (m+1)))) :=
    of_eq (by simp only [E1, SyntaxIdentityMapSyntax.identityCode_rename]; rfl) (HornBinderRules.under_body 2 hE1 E2)
  let vals : Fin 4 → Fin (m+4) := Fin.cases (old 3 (Fin.last m))
    (Fin.cases (old 2 (Fin.last (m+1))) (Fin.cases (slot 2 0) (fun _ => slot 2 1)))
  have ho : Derives Δ4 (promoted (old 4 w) (old 4 z) (old 4 b) (old 4 A) (old 4 G)) := by
    apply HornBinderRules.intro_many 4 _ vals
    exact of_eq (by simp only [promotedBody, promotedData_rename, assign_old, assign_slot]; rfl)
      (.conjI hI4 (.conjI hJ4 (.conjI hE2 (.conjI hm ht))))
  exact of_eq (by simp only [Formula.raise, promoted_rename]; rfl) ho

theorem closed_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A G : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hG : Derives Γ (formulaCode w G z b)) :
    Derives Γ (formulaCode w G A b) := by
  let E := promotedBody w z b A G
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (promote hZ w z b A G hw hz hA hG)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (formulaCode_rename w G A b (old 4)).symm (.conjR (.conjR (.conjR (.conjR hE))))

def sentence {m} (w z b A G : Fin m) : Source.Sentence :=
  (((omega w).conj ((empty z).conj ((successor A z).conj (formulaCode w G z b)))).imp (promoted w z b A G)).close

theorem kernel_certificate {m} (w z b A G : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z b A G)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (omega w).conj ((empty z).conj ((successor A z).conj (formulaCode w G z b)))
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact promote (ZFContext.add (ZFContext.source_ZF m) E) w z b A G (.conjL hE)
    (.conjL (.conjR hE)) (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))

private theorem identity_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d I J R S x u : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (diagonalCode w a c I))
    (hJ : Derives Γ (diagonalCode w b d J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x u)) :
    Derives Γ (.equal x u) := by
  let B := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc c.castSucc I.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hI
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hJ1 := of_eq (diagonalCode_rename w b d J Fin.castSucc) (under hJ B)
  let E := (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc J.castSucc.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last (m+1)))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) hJ1
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hB2 : Derives Ξ ((SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc I.castSucc.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m).castSucc)) := of_eq
    (by simp only [B, Formula.raise, Formula.rename, SyntaxMapCodeSyntax.encoded_rename, SyntaxRenameTermIdentity.diagonal_rename]) (under hB E)
  have hZ2 := ZFContext.under (ZFContext.under hZ B) E
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) E)
  have he2 : Derives Ξ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (under (under he B) E)
  have hq2 : Derives Ξ (SyntaxCodedMixedTermSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedTermSyntax.substituted_rename]) (under (under hq B) E)
  have hp := Derives.impE (Derives.conjR (TermTransformProgramCorrectness.checked_iff hZ2
    w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
    x.castSucc.castSucc u.castSucc.castSucc hw2)) hq2
  have hr := Derives.impE (Derives.conjL (IndexTermImageEnvironment.term_program_iff hZ2
    w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc u.castSucc.castSucc hw2 he2 (Derives.conjL hB2) (Derives.conjL hE))) hp
  exact SyntaxRenameTermIdentity.identity hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc
    hw2 (Derives.conjR hB2) (Derives.conjR hE) hr


/-- The DIRECT promoted leg on arbitrary actual term candidates. Reuse the
existing raw term identity and actual index/mixed environment, not a second
term recursion. This is consumed by the weak/abstract four-path diagram. -/
theorem promoted_term_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A G x q : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hv : Derives Γ (promotedData w z b A G v))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (v 2) (v 3) z b A b x q)) :
    Derives Γ (.equal x q) :=
  identity_term hZ w z b A b (v 0) (v 1) (v 2) (v 3) x q hw
    (empty_shift w z A (v 0) hz (.conjL hv)) (.conjL (.conjR hv))
    (.conjL (.conjR (.conjR hv))) hq

end PPAC.Migration.ForcingScopeIdentity

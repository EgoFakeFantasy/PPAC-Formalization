import PPAC.Migration.ForcingFreshPreorder
import PPAC.Migration.ForcingPreorderLeafTarget

/-! Connect the SAME source fresh-preorder producer directly to the existing
target-to-leaves consumer. Original native/matrix/background/prefix witnesses
remain object-bound; none of those producers or readers is reimplemented. -/
namespace PPAC.Migration.ForcingFreshLeaves
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def conditions {m} (x : Fin 6 → Fin m) : Fin 3 → Fin m :=
  Fin.cases (x 0) (SyntaxAtomSyntax.two (x 1) (x 2))
private theorem conditions_map {m l} (x : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (conditions x i)) = conditions (fun j => ρ (x j)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.cases rfl (fun e => Fin.elim0 e) i)) i

def input {k m} (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral 3 A3).conj
      (ForcingFreshPreorder.input Reln w z A1 A2 A3 f b A B R S q p Pre raw v))))

theorem input_rename {k m l} (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v).rename ρ =
      input Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) := by
  simp only [input, Formula.rename, SyntaxNumeralSyntax.numeral_rename, ForcingFreshPreorder.input_rename]

def data {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (x : Fin 6 → Fin m) : Formula m :=
  (ForcingFreshPreorder.data test Reln w z A1 A2 A3 f b A B R S q p Pre raw v x).conj
    (ForcingPreorderLeafTarget.instances test Reln w z A1 A2 A3 f B A (v 8) (v 9) (x 4) (x 3) (x 5) raw (conditions x))

theorem data_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (x : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (data test Reln w z A1 A2 A3 f b A B R S q p Pre raw v x).rename ρ =
      data test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) (fun j => ρ (x j)) := by
  simp only [data, Formula.rename, ForcingFreshPreorder.data_rename, ForcingPreorderLeafTarget.instances_rename, conditions_map]

def body {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula (m+6) :=
  data test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 b) (old 6 A) (old 6 B)
    (old 6 R) (old 6 S) (old 6 q) (old 6 p) (old 6 Pre) (fun j => old 6 (raw j)) (fun j => old 6 (v j)) (slot 6)

def produced {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 6 (body test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)

theorem produced_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v).rename ρ =
      produced test Reln (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ A3) (ρ f) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ q) (ρ p) (ρ Pre)
        (fun j => ρ (raw j)) (fun j => ρ (v j)) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- Invoke both existing consumers on the SAME actual raw source and fresh
output. No independently supplied native instance or leaf-row answer. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b A B R S q p Pre : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (input Reln w z A1 A2 A3 f b A B R S q p Pre raw v)) :
    Derives Γ (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v) := by
  have hs := Derives.conjR (.conjR (.conjR (.conjR hi)))
  let E := ForcingFreshPreorder.body test Reln w z A1 A2 A3 f b A B R S q p Pre raw v
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ (ForcingFreshPreorder.produce hZ test Reln w z A1 A2 A3 f b A B R S q p Pre raw v hs)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h6 := of_eq (input_rename Reln w z A1 A2 A3 f b A B R S q p Pre raw v (old 6)) (HornBinderRules.under_body 6 hi E)
  have hSource := Derives.conjL hE
  have hBase := Derives.conjL (.conjR (.conjR hSource))
  have hRaw := Derives.conjL (.conjR (.conjR (.conjR hSource)))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hE)))))
  have hLeaves := ForcingPreorderLeafTarget.at_target (HornBinderRules.zf_body 6 hZ E) test Reln
    (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f) (old 6 B) (old 6 A)
    (old 6 (v 8)) (old 6 (v 9)) (slot 6 4) (slot 6 3) (slot 6 5) (fun j => old 6 (raw j)) (conditions (slot 6))
    (.conjL (.conjL hBase)) (.conjL h6) (.conjL (.conjR h6)) (.conjL (.conjR (.conjR h6)))
    (.conjL (.conjR (.conjR (.conjR h6)))) hRaw ht
  have hd : Derives Δ (data test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f)
      (old 6 b) (old 6 A) (old 6 B) (old 6 R) (old 6 S) (old 6 q) (old 6 p) (old 6 Pre)
      (fun j => old 6 (raw j)) (fun j => old 6 (v j)) (slot 6)) := .conjI hE hLeaves
  have ho : Derives Δ (produced test Reln (old 6 w) (old 6 z) (old 6 A1) (old 6 A2) (old 6 A3) (old 6 f)
      (old 6 b) (old 6 A) (old 6 B) (old 6 R) (old 6 S) (old 6 q) (old 6 p) (old 6 Pre)
      (fun j => old 6 (raw j)) (fun j => old 6 (v j))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (produced_rename test Reln w z A1 A2 A3 f b A B R S q p Pre raw v (old 6)).symm ho

def sentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : Source.Sentence :=
  ((input Reln w z A1 A2 A3 f b A B R S q p Pre raw v).imp
    (produced test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)).close

theorem kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (w z A1 A2 A3 f b A B R S q p Pre : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test Reln w z A1 A2 A3 f b A B R S q p Pre raw v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z A1 A2 A3 f b A B R S q p Pre raw v (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingFreshLeaves

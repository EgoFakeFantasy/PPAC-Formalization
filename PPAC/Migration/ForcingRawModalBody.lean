import PPAC.Migration.ForcingRawGuardOpening
import PPAC.Migration.ForcingExistTailComparison
import PPAC.Migration.ForcingRawNegTail

/-! The two outer implications of the original negative and existential
compilers, queried in the actual fresh table of the opened parent. -/
namespace PPAC.Migration.ForcingRawModalBody
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Target witnesses are the member guard, inner implication, order guard
and tail. Both target constructors and all three raw queries are retained. -/
def data {m} (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingFormulaDiagram.binaryData 2 w D S a f z T M I Y (v 1) (v 0)).conj
    (ForcingFormulaDiagram.binaryData 2 w D S a f z T O L (v 0) (v 2) (v 3))

theorem data_rename {m l} (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (data w D S a f z T M O L I Y v).rename rho =
      data (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) (fun i => rho (v i)) := by
  simp only [data, Formula.rename, ForcingFormulaDiagram.binaryData_rename]

def outputs {m} (w D S a f z T M O L I Y : Fin m) : Formula m :=
  existsMany 4 (data (old 4 w) (old 4 D) (old 4 S) (old 4 a) (old 4 f) (old 4 z) (old 4 T)
    (old 4 M) (old 4 O) (old 4 L) (old 4 I) (old 4 Y) (slot 4))

theorem outputs_rename {m l} (w D S a f z T M O L I Y : Fin m) (rho : Fin m → Fin l) :
    (outputs w D S a f z T M O L I Y).rename rho =
      outputs (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) := by
  simp only [outputs, existsMany_rename, data_rename, lift_old, lift_slot]

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (SyntaxAtomSyntax.two c d))

theorem from_query {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w D S a f z T M O L I X Y : Fin m) (hw : Derives Gamma (omega w))
    (houter : Derives Gamma (binaryCode 2 w M I X))
    (hinner : Derives Gamma (binaryCode 2 w O L I))
    (hq : Derives Gamma (substituted w D S a f z T X Y)) :
    Derives Gamma (outputs w D S a f z T M O L I Y) := by
  let E := ForcingFormulaDiagram.binaryBody 2 w D S a f z T M I Y
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _
    (ForcingFormulaDiagram.binary_output hZ 2 w D S a f z T X M I Y hw houter hq)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hinner2 := of_eq (binaryCode_rename 2 w O L I (old 2)) (HornBinderRules.under_body 2 hinner E)
  let F := ForcingFormulaDiagram.binaryBody 2 (old 2 w) (old 2 D) (old 2 S)
    (old 2 a) (old 2 f) (old 2 z) (old 2 T) (old 2 O) (old 2 L) (slot 2 1)
  let Xi := Context.add F (raisedContext 2 Delta)
  apply HornBinderRules.eliminate_many 2 F _
    (ForcingFormulaDiagram.binary_output (HornBinderRules.zf_body 2 hZ E) 2
      (old 2 w) (old 2 D) (old 2 S) (old 2 a) (old 2 f) (old 2 z) (old 2 T)
      (old 2 I) (old 2 O) (old 2 L) (slot 2 1) hw2 hinner2 (.conjR (.conjR he)))
  have hf : Derives Xi F := .hyp (Or.inl rfl)
  have he4 := of_eq (ForcingFormulaDiagram.binaryData_rename 2 (old 2 w) (old 2 D) (old 2 S)
    (old 2 a) (old 2 f) (old 2 z) (old 2 T) (old 2 M) (old 2 I) (old 2 Y)
    (slot 2 0) (slot 2 1) (old 2)) (HornBinderRules.under_body 2 he F)
  have out : Derives Xi (outputs (old 2 (old 2 w)) (old 2 (old 2 D)) (old 2 (old 2 S))
      (old 2 (old 2 a)) (old 2 (old 2 f)) (old 2 (old 2 z)) (old 2 (old 2 T))
      (old 2 (old 2 M)) (old 2 (old 2 O)) (old 2 (old 2 L)) (old 2 (old 2 I)) (old 2 (old 2 Y))) := by
    apply HornBinderRules.intro_many 4 _ (four (old 2 (slot 2 1)) (old 2 (slot 2 0)) (slot 2 0) (slot 2 1))
    exact of_eq (by simp only [data_rename, assign_old, assign_slot]; rfl) (.conjI he4 hf)
  exact of_eq (by simp only [outputs_rename]) out

/-- Source constructor fields read from either literal compiler shell. -/
def shell {m} (w n M O L I X : Fin m) : Formula m :=
  (singleCode 9 w X n).conj ((binaryCode 2 w M I X).conj (binaryCode 2 w O L I))

theorem shell_rename {m l} (w n M O L I X : Fin m) (rho : Fin m → Fin l) :
    (shell w n M O L I X).rename rho = shell (rho w) (rho n) (rho M) (rho O) (rho L) (rho I) (rho X) := by
  simp only [shell, Formula.rename, singleCode_rename, binaryCode_rename]

private theorem at_opened {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z a f alpha b A B t R S n x Parent M O L I X : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hs : Derives Gamma (shell w n M O L I X)) :
    Derives Gamma (outputs w (u 7) (v 9) alpha f z B M O L I (u 8)) := by
  have src := Derives.conjL hp
  have hw := Derives.conjL src
  have all := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src)))))))
  have raw := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hp))))))))
  have eq := SyntaxLogicalFields.single_fields hZ 9 w x X n hw all (.conjL hs)
  have hq := SyntaxMixedFormulaJudgmentSubst.subst_n w (u 7) (v 9) alpha f z B x (u 8) X eq raw
  exact from_query hZ w (u 7) (v 9) alpha f z B M O L I X (u 8) hw (.conjL (.conjR hs)) (.conjR (.conjR hs)) hq

def guardData {k m} (Reln : Source.Formula (k+2)) (w D S a f z T P head M O L I Y : Fin m)
    (v : Fin 4 → Fin m) : Formula m :=
  (data w D S a f z T M O L I Y v).conj
    ((ForcingGuardOpening.result false Reln w z f T P S a head M (v 1)).conj
      (ForcingGuardOpening.result true Reln w z f T P S a head O (v 2)))

theorem guardData_rename {k m l} (Reln : Source.Formula (k+2)) (w D S a f z T P head M O L I Y : Fin m)
    (v : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (guardData Reln w D S a f z T P head M O L I Y v).rename rho =
      guardData Reln (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho P) (rho head) (rho M) (rho O) (rho L) (rho I) (rho Y) (fun i => rho (v i)) := by
  simp only [guardData, Formula.rename, data_rename, ForcingGuardOpening.result_rename]

def guarded {k m} (Reln : Source.Formula (k+2)) (w D S a f z T P head M O L I Y : Fin m) : Formula m :=
  existsMany 4 (guardData Reln (old 4 w) (old 4 D) (old 4 S) (old 4 a) (old 4 f) (old 4 z) (old 4 T)
    (old 4 P) (old 4 head) (old 4 M) (old 4 O) (old 4 L) (old 4 I) (old 4 Y) (slot 4))

theorem guarded_rename {k m l} (Reln : Source.Formula (k+2)) (w D S a f z T P head M O L I Y : Fin m)
    (rho : Fin m → Fin l) :
    (guarded Reln w D S a f z T P head M O L I Y).rename rho =
      guarded Reln (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho P) (rho head) (rho M) (rho O) (rho L) (rho I) (rho Y) := by
  simp only [guarded, existsMany_rename, guardData_rename, lift_old, lift_slot]

theorem from_shell {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head M O L I X : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hs : Derives Gamma (shell w n M O L I X))
    (hh : Derives Gamma (SyntaxMixedImageHead.head w alpha f own head))
    (hm : Derives Gamma (ForcingGuardCode.compiled false Reln w alpha f head M))
    (ho : Derives Gamma (ForcingGuardCode.compiled true Reln w alpha f head O)) :
    Derives Gamma (guarded Reln w (u 7) (v 9) alpha f z B t head M O L I (u 8)) := by
  let F := data (old 4 w) (old 4 (u 7)) (old 4 (v 9)) (old 4 alpha) (old 4 f) (old 4 z) (old 4 B)
    (old 4 M) (old 4 O) (old 4 L) (old 4 I) (old 4 (u 8)) (slot 4)
  let Delta := Context.add F (raisedContext 4 Gamma)
  apply HornBinderRules.eliminate_many 4 F _
    (at_opened hZ w z a f alpha b A B t R S n x Parent M O L I X v u hp hs)
  have hF : Derives Delta F := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ F
  have hp4 := of_eq (ForcingFreshParentOpening.data_rename w z a f alpha b A B t R S n x Parent v u (old 4))
    (HornBinderRules.under_body 4 hp F)
  have hh4 := of_eq (SyntaxMixedImageHead.head_rename w alpha f own head (old 4)) (HornBinderRules.under_body 4 hh F)
  have hm4 := of_eq (ForcingGuardCode.compiled_rename false Reln w alpha f head M (old 4)) (HornBinderRules.under_body 4 hm F)
  have ho4 := of_eq (ForcingGuardCode.compiled_rename true Reln w alpha f head O (old 4)) (HornBinderRules.under_body 4 ho F)
  have gM := ForcingRawGuardOpening.from_opened hZ4 false Reln
    (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 alpha) (old 4 b) (old 4 A) (old 4 B)
    (old 4 t) (old 4 R) (old 4 S) (old 4 n) (old 4 x) (old 4 Parent) (old 4 own) (old 4 head)
    (old 4 M) (slot 4 1) (fun i => old 4 (v i)) (fun i => old 4 (u i))
    (.conjI hp4 (.conjI hh4 (.conjI hm4 (.conjL (.conjR (.conjL hF))))))
  have gO := ForcingRawGuardOpening.from_opened hZ4 true Reln
    (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 alpha) (old 4 b) (old 4 A) (old 4 B)
    (old 4 t) (old 4 R) (old 4 S) (old 4 n) (old 4 x) (old 4 Parent) (old 4 own) (old 4 head)
    (old 4 O) (slot 4 2) (fun i => old 4 (v i)) (fun i => old 4 (u i))
    (.conjI hp4 (.conjI hh4 (.conjI ho4 (.conjL (.conjR (.conjR hF))))))
  have out : Derives Delta (guarded Reln (old 4 w) (old 4 (u 7)) (old 4 (v 9)) (old 4 alpha)
      (old 4 f) (old 4 z) (old 4 B) (old 4 t) (old 4 head) (old 4 M) (old 4 O) (old 4 L) (old 4 I) (old 4 (u 8))) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [guardData_rename, assign_old, assign_slot]; rfl) (.conjI hF (.conjI gM gO))
  exact of_eq (guarded_rename Reln w (u 7) (v 9) alpha f z B t head M O L I (u 8) (old 4)).symm out

def negativeRecord {k m} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u).conj
    ((ForcingNegCode.data Reln w a alpha f j N n cv).conj
    ((ForcingNegCode.shellData w a alpha f (cv 3) (cv 4) (cv 2) n sv).conj
      (guarded Reln w (u 7) (v 9) alpha f z B t (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (u 8))))

theorem negativeRecord_rename {k m l} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (negativeRecord Reln w z a f alpha b A B t R S j N n x Parent v u cv sv).rename rho =
      negativeRecord Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho j) (rho N) (rho n) (rho
        x) (rho Parent)
        (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (cv i)) (fun i => rho (sv i)) := by
  simp only [negativeRecord, Formula.rename, ForcingFreshParentOpening.data_rename, ForcingNegCode.data_rename, ForcingNegCode.shellData_rename,
    guarded_rename]

def negativeAt {k m} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 5 → Fin m) : Formula m :=
  existsMany 4 (negativeRecord Reln (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 alpha) (old 4 b) (old 4 A) (old 4 B) (old 4 t) (old 4 R) (old 4
    S) (old 4 j) (old 4 N) (old 4 n) (old 4 x) (old 4 Parent)
    (fun i => old 4 (v i)) (fun i => old 4 (u i)) (fun i => old 4 (cv i)) (slot 4))

theorem negativeAt_rename {k m l} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 5 → Fin m) (rho : Fin m → Fin l) :
    (negativeAt Reln w z a f alpha b A B t R S j N n x Parent v u cv).rename rho =
      negativeAt Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho j) (rho N) (rho n) (rho x)
        (rho Parent) (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (cv i)) := by
  simp only [negativeAt, existsMany_rename, negativeRecord_rename, lift_old, lift_slot]

def negative {k m} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Formula m :=
  existsMany 5 (negativeAt Reln (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 alpha) (old 5 b) (old 5 A) (old 5 B) (old 5 t) (old 5 R) (old 5 S)
    (old 5 j) (old 5 N) (old 5 n) (old 5 x) (old 5 Parent) (fun i => old 5 (v i)) (fun i => old 5 (u i)) (slot 5))

theorem negative_rename {k m l} (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (rho : Fin m → Fin l) :
    (negative Reln w z a f alpha b A B t R S j N n x Parent v u).rename rho =
      negative Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho j) (rho N) (rho n) (rho x)
        (rho Parent) (fun i => rho (v i)) (fun i => rho (u i)) := by
  simp only [negative, existsMany_rename, negativeAt_rename, lift_old, lift_slot]

private theorem negative_at_records {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hc : Derives Gamma (ForcingNegCode.data Reln w a alpha f j N n cv))
    (hs : Derives Gamma (ForcingNegCode.shellData w a alpha f (cv 3) (cv 4) (cv 2) n sv)) :
    Derives Gamma (negativeRecord Reln w z a f alpha b A B t R S j N n x Parent v u cv sv) := by
  have head := Derives.conjL hc
  have hShell : Derives Gamma (shell w n (cv 3) (cv 4) (sv 1) (sv 2) (sv 3)) :=
    .conjI (.conjL (.conjR (.conjR (.conjR (.conjR hs))))) (.conjI (.conjL (.conjL (.conjR (.conjR (.conjR hs))))) (.conjL (.conjL (.conjR (.conjR
      hs)))))
  exact .conjI hp (.conjI hc (.conjI hs (from_shell hZ Reln w z a f alpha b A B t R S n x Parent
    (cv 0) (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (sv 3)
    v u hp hShell head (.conjL (.conjR (.conjR hc))) (.conjL (.conjR (.conjR (.conjR hc)))))))

/-- Read the literal outer constructors from the complete negative compiler. -/
theorem from_negative {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (Reln : Source.Formula (k+2)) (w z a f alpha b A B t R S j N n x Parent : Fin m) (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hc : Derives Gamma (ForcingNegCode.compiled Reln w a alpha f j N n)) :
    Derives Gamma (negative Reln w z a f alpha b A B t R S j N n x Parent v u) := by
  let E := ForcingNegCode.body Reln w a alpha f j N n
  let Delta := Context.add E (raisedContext 5 Gamma)
  apply HornBinderRules.eliminate_many 5 E _ (.conjR hc)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  let F := ForcingNegCode.shellBody (old 5 w) (old 5 a) (old 5 alpha) (old 5 f) (slot 5 3) (slot 5 4) (slot 5 2) (old 5 n)
  let Xi := Context.add F (raisedContext 4 Delta)
  apply HornBinderRules.eliminate_many 4 F _ (.conjR (.conjR (.conjR (.conjR he))))
  have hf : Derives Xi F := .hyp (Or.inl rfl)
  have hp1 := of_eq (ForcingFreshParentOpening.data_rename w z a f alpha b A B t R S n x Parent v u (old 5))
    (HornBinderRules.under_body 5 hp E)
  have hp2 := of_eq (ForcingFreshParentOpening.data_rename (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 alpha) (old 5 b) (old 5 A) (old 5 B)
    (old 5 t) (old 5 R) (old 5 S) (old 5 n) (old 5 x) (old 5 Parent)
    (fun i => old 5 (v i)) (fun i => old 5 (u i)) (old 4)) (HornBinderRules.under_body 4 hp1 F)
  have he2 : Derives Xi (ForcingNegCode.data Reln (old 4 (old 5 w)) (old 4 (old 5 a)) (old 4 (old 5 alpha)) (old 4 (old 5 f)) (old 4 (old 5 j))
    (old 4 (old 5 N)) (old 4 (old 5 n)) (fun i => old 4 (slot 5 i))) :=
    of_eq (by simp only [E, ForcingNegCode.body, ForcingNegCode.data_rename])
    (HornBinderRules.under_body 4 he F)
  have record := negative_at_records (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 5 hZ E) F)
    Reln (old 4 (old 5 w)) (old 4 (old 5 z)) (old 4 (old 5 a)) (old 4 (old 5 f)) (old 4 (old 5 alpha)) (old 4 (old 5 b)) (old 4 (old 5 A)) (old 4
      (old 5 B)) (old 4 (old 5 t)) (old 4 (old 5 R)) (old 4 (old 5 S)) (old 4 (old 5 j)) (old 4 (old 5 N)) (old 4 (old 5 n)) (old 4 (old 5 x))
      (old 4 (old 5 Parent))
    (fun i => old 4 (old 5 (v i))) (fun i => old 4 (old 5 (u i))) (fun i => old 4 (slot 5 i)) (slot 4) hp2 he2 hf
  have mid : Derives Xi (negativeAt Reln (old 4 (old 5 w)) (old 4 (old 5 z)) (old 4 (old 5 a)) (old 4 (old 5 f)) (old 4 (old 5 alpha)) (old 4 (old
    5 b)) (old 4 (old 5 A)) (old 4 (old 5 B)) (old 4 (old 5 t)) (old 4 (old 5 R)) (old 4 (old 5 S)) (old 4 (old 5 j)) (old 4 (old 5 N)) (old 4
    (old 5 n)) (old 4 (old 5 x)) (old 4 (old 5 Parent))
      (fun i => old 4 (old 5 (v i))) (fun i => old 4 (old 5 (u i))) (fun i => old 4 (slot 5 i))) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [negativeRecord_rename, assign_old, assign_slot]) record
  have out : Derives Xi (negative Reln (old 4 (old 5 w)) (old 4 (old 5 z)) (old 4 (old 5 a)) (old 4 (old 5 f)) (old 4 (old 5 alpha)) (old 4 (old 5
    b)) (old 4 (old 5 A)) (old 4 (old 5 B)) (old 4 (old 5 t)) (old 4 (old 5 R)) (old 4 (old 5 S)) (old 4 (old 5 j)) (old 4 (old 5 N)) (old 4 (old
    5 n)) (old 4 (old 5 x)) (old 4 (old 5 Parent))
      (fun i => old 4 (old 5 (v i))) (fun i => old 4 (old 5 (u i)))) := by
    apply HornBinderRules.intro_many 5 _ (fun i => old 4 (slot 5 i))
    exact of_eq (by simp only [negativeAt_rename, assign_old, assign_slot]) mid
  exact of_eq (by simp only [negative_rename]) out

def existentialRecord {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent : Fin
  m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u).conj
    ((ForcingExistCode.data Reln Dom w a alpha beta gamma f j N n cv).conj
    ((ForcingExistCode.shellData w a alpha beta gamma f (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) n sv).conj
      (guarded Reln w (u 7) (v 9) alpha f z B t (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (u 8))))

theorem existentialRecord_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x
  Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (rho : Fin m → Fin l) :
    (existentialRecord Reln Dom w z a f alpha beta gamma b A B t R S j N n x Parent v u cv sv).rename rho =
      existentialRecord Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A) (rho B) (rho t) (rho R) (rho
        S) (rho j) (rho N) (rho n) (rho x) (rho Parent)
        (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (cv i)) (fun i => rho (sv i)) := by
  simp only [existentialRecord, Formula.rename, ForcingFreshParentOpening.data_rename, ForcingExistCode.data_rename,
    ForcingExistCode.shellData_rename, guarded_rename]

def existentialAt {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) : Formula m :=
  existsMany 7 (existentialRecord Reln Dom (old 7 w) (old 7 z) (old 7 a) (old 7 f) (old 7 alpha) (old 7 beta) (old 7 gamma) (old 7 b) (old 7 A)
    (old 7 B) (old 7 t) (old 7 R) (old 7 S) (old 7 j) (old 7 N) (old 7 n) (old 7 x) (old 7 Parent)
    (fun i => old 7 (v i)) (fun i => old 7 (u i)) (fun i => old 7 (cv i)) (slot 7))

theorem existentialAt_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x
  Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (rho : Fin m → Fin l) :
    (existentialAt Reln Dom w z a f alpha beta gamma b A B t R S j N n x Parent v u cv).rename rho =
      existentialAt Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S)
        (rho j) (rho N) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (cv i)) := by
  simp only [existentialAt, existsMany_rename, existentialRecord_rename, lift_old, lift_slot]

def existential {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Formula m :=
  existsMany 8 (existentialAt Reln Dom (old 8 w) (old 8 z) (old 8 a) (old 8 f) (old 8 alpha) (old 8 beta) (old 8 gamma) (old 8 b) (old 8 A) (old 8
    B) (old 8 t) (old 8 R) (old 8 S) (old 8 j) (old 8 N) (old 8 n) (old 8 x) (old 8 Parent) (fun i => old 8 (v i)) (fun i => old 8 (u i)) (slot
    8))

theorem existential_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent
  : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (rho : Fin m → Fin l) :
    (existential Reln Dom w z a f alpha beta gamma b A B t R S j N n x Parent v u).rename rho =
      existential Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A) (rho B) (rho t) (rho R) (rho S) (rho
        j) (rho N) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) (fun i => rho (u i)) := by
  simp only [existential, existsMany_rename, existentialAt_rename, lift_old, lift_slot]

private theorem head_at_parent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f alpha b A B t R S n x Parent gamma own h : Fin m)
    (hp : Derives Γ (ForcingFreshParentOpening.input w z a f alpha b A B t R S n x Parent))
    (head : Derives Γ (SyntaxMixedImageHead.head w gamma f own h)) :
    Derives Γ (SyntaxMixedImageHead.head w alpha f own h) := by
  have typing := SyntaxMixedFormulaJudgmentTyping.source_type hZ w R S a f z b n Parent
    (.conjL hp) (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hp))))))))
  have range := Derives.conjR (FormulaCodeProperties.guards w n a f typing)
  exact .conjI (.conjL head) (.conjI (.conjL (.conjR head))
    (SyntaxMixedImageHead.term_at_zero hZ w a alpha f own h (.conjL hp)
      (.conjL range) (.conjR range) (.conjL (.conjR (.conjR hp))) (.conjL head) (.conjL (.conjR head))))

private theorem existential_at_records {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hc : Derives Gamma (ForcingExistCode.data Reln Dom w a alpha beta gamma f j N n cv))
    (hs : Derives Gamma (ForcingExistCode.shellData w a alpha beta gamma f (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) n sv)) :
    Derives Gamma (existentialRecord Reln Dom w z a f alpha beta gamma b A B t R S j N n x Parent v u cv sv) := by
  have headAtAlpha := head_at_parent hZ w z a f alpha b A B t R S n x Parent gamma
    (cv 0) (cv 1) (.conjL hp) (.conjL hc)
  have hShell : Derives Gamma (shell w n (cv 2) (cv 3) (sv 4) (sv 5) (sv 6)) :=
    .conjI (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hs)))))))) (.conjI (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR
      (.conjR (.conjR hs)))))))) (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hs))))))))
  exact .conjI hp (.conjI hc (.conjI hs (from_shell hZ Reln w z a f alpha b A B t R S n x Parent
    (cv 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (sv 6)
    v u hp hShell headAtAlpha (.conjL (.conjR hc)) (.conjL (.conjR (.conjR hc))))))

/-- Read the literal outer constructors from the complete existential compiler. -/
theorem from_existential {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1)) (w z a f alpha beta gamma b A B t R S j N n x Parent : Fin m) (v : Fin 10 → Fin m)
      (u : Fin 9 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hc : Derives Gamma (ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n)) :
    Derives Gamma (existential Reln Dom w z a f alpha beta gamma b A B t R S j N n x Parent v u) := by
  let E := ForcingExistCode.body Reln Dom w a alpha beta gamma f j N n
  let Delta := Context.add E (raisedContext 8 Gamma)
  apply HornBinderRules.eliminate_many 8 E _ (.conjR hc)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  let F := ForcingExistCode.shellBody (old 8 w) (old 8 a) (old 8 alpha) (old 8 beta) (old 8 gamma) (old 8 f) (slot 8 2) (slot 8 3) (slot 8 4)
    (slot 8 5) (slot 8 6) (slot 8 7) (old 8 n)
  let Xi := Context.add F (raisedContext 7 Delta)
  apply HornBinderRules.eliminate_many 7 F _ (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR he)))))))
  have hf : Derives Xi F := .hyp (Or.inl rfl)
  have hp1 := of_eq (ForcingFreshParentOpening.data_rename w z a f alpha b A B t R S n x Parent v u (old 8))
    (HornBinderRules.under_body 8 hp E)
  have hp2 := of_eq (ForcingFreshParentOpening.data_rename (old 8 w) (old 8 z) (old 8 a) (old 8 f) (old 8 alpha) (old 8 b) (old 8 A) (old 8 B)
    (old 8 t) (old 8 R) (old 8 S) (old 8 n) (old 8 x) (old 8 Parent)
    (fun i => old 8 (v i)) (fun i => old 8 (u i)) (old 7)) (HornBinderRules.under_body 7 hp1 F)
  have he2 : Derives Xi (ForcingExistCode.data Reln Dom (old 7 (old 8 w)) (old 7 (old 8 a)) (old 7 (old 8 alpha)) (old 7 (old 8 beta)) (old 7 (old
    8 gamma)) (old 7 (old 8 f)) (old 7 (old 8 j)) (old 7 (old 8 N)) (old 7 (old 8 n)) (fun i => old 7 (slot 8 i))) :=
    of_eq (by simp only [E, ForcingExistCode.body, ForcingExistCode.data_rename])
    (HornBinderRules.under_body 7 he F)
  have record := existential_at_records (HornBinderRules.zf_body 7 (HornBinderRules.zf_body 8 hZ E) F)
    Reln Dom (old 7 (old 8 w)) (old 7 (old 8 z)) (old 7 (old 8 a)) (old 7 (old 8 f)) (old 7 (old 8 alpha)) (old 7 (old 8 beta)) (old 7 (old 8
      gamma)) (old 7 (old 8 b)) (old 7 (old 8 A)) (old 7 (old 8 B)) (old 7 (old 8 t)) (old 7 (old 8 R)) (old 7 (old 8 S)) (old 7 (old 8 j)) (old 7
      (old 8 N)) (old 7 (old 8 n)) (old 7 (old 8 x)) (old 7 (old 8 Parent))
    (fun i => old 7 (old 8 (v i))) (fun i => old 7 (old 8 (u i))) (fun i => old 7 (slot 8 i)) (slot 7) hp2 he2 hf
  have mid : Derives Xi (existentialAt Reln Dom (old 7 (old 8 w)) (old 7 (old 8 z)) (old 7 (old 8 a)) (old 7 (old 8 f)) (old 7 (old 8 alpha)) (old
    7 (old 8 beta)) (old 7 (old 8 gamma)) (old 7 (old 8 b)) (old 7 (old 8 A)) (old 7 (old 8 B)) (old 7 (old 8 t)) (old 7 (old 8 R)) (old 7 (old 8
    S)) (old 7 (old 8 j)) (old 7 (old 8 N)) (old 7 (old 8 n)) (old 7 (old 8 x)) (old 7 (old 8 Parent))
      (fun i => old 7 (old 8 (v i))) (fun i => old 7 (old 8 (u i))) (fun i => old 7 (slot 8 i))) := by
    apply HornBinderRules.intro_many 7 _ (slot 7)
    exact of_eq (by simp only [existentialRecord_rename, assign_old, assign_slot]) record
  have out : Derives Xi (existential Reln Dom (old 7 (old 8 w)) (old 7 (old 8 z)) (old 7 (old 8 a)) (old 7 (old 8 f)) (old 7 (old 8 alpha)) (old 7
    (old 8 beta)) (old 7 (old 8 gamma)) (old 7 (old 8 b)) (old 7 (old 8 A)) (old 7 (old 8 B)) (old 7 (old 8 t)) (old 7 (old 8 R)) (old 7 (old 8
    S)) (old 7 (old 8 j)) (old 7 (old 8 N)) (old 7 (old 8 n)) (old 7 (old 8 x)) (old 7 (old 8 Parent))
      (fun i => old 7 (old 8 (v i))) (fun i => old 7 (old 8 (u i)))) := by
    apply HornBinderRules.intro_many 8 _ (fun i => old 7 (slot 8 i))
    exact of_eq (by simp only [existentialAt_rename, assign_old, assign_slot]) mid
  exact of_eq (by simp only [existential_rename]) out

private theorem imp_operands {m} {Gamma : Context m} (w a b c d n : Fin m)
    (ha : Derives Gamma (.equal a c)) (hb : Derives Gamma (.equal b d))
    (h : Derives Gamma (binaryCode 2 w a b n)) : Derives Gamma (binaryCode 2 w c d n) := by
  let L := binaryCode 2 w.castSucc (Fin.last m) b.castSucc n.castSucc
  have hL : Derives Gamma (binaryCode 2 w c b n) := by
    have ht := Derives.eqSubst L ha (of_eq (by
      simp only [L, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h)
    exact of_eq (by
      simp only [L, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht
  let R := binaryCode 2 w.castSucc c.castSucc (Fin.last m) n.castSucc
  have ht := Derives.eqSubst R hb (of_eq (by
    simp only [R, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hL)
  exact of_eq (by
    simp only [R, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht

/-- The three leaf equalities determine the whole opened body by original
constructor uniqueness. The source Root consumer receives that same body. -/
theorem consume_matched {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (test : Formula 1)
    (w z a f alpha b A B t R S n x Parent sm so st si G W M O Tail I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (r : Fin 4 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hr : Derives Gamma (data w (u 7) (v 9) alpha f z B sm so st si (u 8) r))
    (hn : Derives Gamma (ForcingNestedGuardProof.data test w z b A B G W M O Tail I K J))
    (hm : Derives Gamma (.equal (r 1) M))
    (ho : Derives Gamma (.equal (r 2) O))
    (ht : Derives Gamma (.equal (r 3) Tail)) :
    Derives Gamma (InternalProofBackground.implication test w z b G Parent) := by
  have hw := Derives.conjL (.conjL hp)
  have inner := imp_operands w (r 2) (r 3) O Tail (r 0) ho ht (.conjL (.conjR hr))
  have eI := SyntaxLogicalFields.binary_unique hZ 2 w O Tail (r 0) I hw inner (.conjL (.conjL hn))
  have outer := imp_operands w (r 1) (r 0) M I (u 8) hm eI (.conjL (.conjL hr))
  have eK := SyntaxLogicalFields.binary_unique hZ 2 w M I K (u 8) hw (.conjL (.conjR (.conjL hn))) outer
  let F := ForcingNestedGuardProof.data test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc
    G.castSucc W.castSucc M.castSucc O.castSucc Tail.castSucc I.castSucc (Fin.last m) J.castSucc
  have hF := Derives.eqSubst F eK (of_eq (by simp only [F, Formula.instantiate, ForcingNestedGuardProof.data_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn)
  have moved : Derives Gamma (ForcingNestedGuardProof.data test w z b A B G W M O Tail I (u 8) J) :=
    of_eq (by simp only [F, Formula.instantiate, ForcingNestedGuardProof.data_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hF
  exact ForcingFreshParentOpening.consume_opened hZ test w z a f alpha b A B t R S n x Parent
    G W M O Tail I J v u hp moved

private theorem member_atom {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z D S a f T head P i V q Y sym carrier : Fin m)
    (hw : Derives Gamma (omega w)) (hz : Derives Gamma (empty z))
    (hhead : Derives Gamma (SyntaxVariableSyntax.code true w z head))
    (hzero : Derives Gamma (StructuralListFieldSyntax.field w D z P))
    (hi : Derives Gamma (.mem i w)) (hvalue : Derives Gamma (StructuralListFieldSyntax.field w S i V))
    (hsrc : Derives Gamma (ForcingMemberGuard.data w head q i sym carrier))
    (hq : Derives Gamma (substituted w D S a f z T q Y)) :
    Derives Gamma (ForcingMemberGuardOpening.result w P V Y) := by
  have hl := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ w D S a f z T q Y hw hq)
  let E := ForcingFormulaAtoms.atomBody true w sym D S a f z T head carrier Y
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _
    (ForcingFormulaAtoms.atom_output hZ true w sym D S a f z T q head carrier Y hw (.conjR (.conjR hsrc)) hq)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E)
  have hl2 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z T D S (old 2)) (HornBinderRules.under_body 2 hl E)
  have hh2 := of_eq (SyntaxVariableSyntax.code_rename true w z head (old 2)) (HornBinderRules.under_body 2 hhead E)
  have hc2 := of_eq (ForcingMemberGuard.data_rename w head q i sym carrier (old 2)) (HornBinderRules.under_body 2 hsrc E)
  have fieldP := Derives.conjR (Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 true
    (old 2 w) (old 2 D) (old 2 S) (old 2 a) (old 2 f) (old 2 z) (old 2 T)
    (old 2 head) (slot 2 0) (old 2 z) hw2 hl2 hh2)) (.conjL (.conjR he)))
  have fieldV := Derives.conjR (Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 false
    (old 2 w) (old 2 D) (old 2 S) (old 2 a) (old 2 f) (old 2 z) (old 2 T)
    (old 2 carrier) (slot 2 1) (old 2 i) hw2 hl2 (.conjL (.conjR hc2)))) (.conjR (.conjR he)))
  have eP := StructuralListFieldValues.unique hZ2 (old 2 w) (old 2 D) (old 2 z) (slot 2 0) (old 2 P)
    hw2 (OmegaStructureAlgebra.zero_member (old 2 w) (old 2 z) (ZFContext.arithmetic hZ2).base.extensionality hw2 hz2)
    fieldP (of_eq (StructuralListFieldSyntax.field_rename w D z P (old 2)) (HornBinderRules.under_body 2 hzero E))
  have eV := StructuralListFieldValues.unique hZ2 (old 2 w) (old 2 S) (old 2 i) (slot 2 1) (old 2 V)
    hw2 (HornBinderRules.under_body 2 hi E) fieldV
    (of_eq (StructuralListFieldSyntax.field_rename w S i V (old 2)) (HornBinderRules.under_body 2 hvalue E))
  have code := SyntaxRenameAtomicSubst.member_y (old 2 w) (old 2 sym) (old 2 P) (slot 2 1) (old 2 Y) (old 2 V) eV
    (SyntaxRenameAtomicSubst.member_x (old 2 w) (old 2 sym) (slot 2 0) (slot 2 1) (old 2 Y) (old 2 P) eP (.conjL he))
  have out : Derives Delta (ForcingMemberGuardOpening.result (old 2 w) (old 2 P) (old 2 V) (old 2 Y)) := by
    apply Derives.exI (old 2 sym)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename,
      SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hc2) code)
  exact of_eq (ForcingMemberGuardOpening.result_rename w P V Y (old 2)).symm out

private theorem member_query {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (Reln : Source.Formula (k+2))
    (w z D S a f T head P i V q Y : Fin m)
    (hw : Derives Gamma (omega w)) (hz : Derives Gamma (empty z))
    (hhead : Derives Gamma (SyntaxVariableSyntax.code true w z head))
    (hzero : Derives Gamma (StructuralListFieldSyntax.field w D z P))
    (hi : Derives Gamma (SyntaxNumeralSyntax.numeral k i)) (hvalue : Derives Gamma (StructuralListFieldSyntax.field w S i V))
    (hc : Derives Gamma (ForcingGuardCode.compiled false Reln w a f head q))
    (hq : Derives Gamma (substituted w D S a f z T q Y)) :
    Derives Gamma (ForcingMemberGuardOpening.result w P V Y) := by
  let E := ForcingMemberGuard.body w head q i
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _ (ForcingMemberGuard.from_compiled hZ Reln w z a f head q i hw hz hi hc)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  have out := member_atom (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 z) (old 2 D) (old 2 S) (old 2 a) (old 2 f) (old 2 T) (old 2 head)
    (old 2 P) (old 2 i) (old 2 V) (old 2 q) (old 2 Y) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head (old 2)) (HornBinderRules.under_body 2 hhead E))
    (of_eq (StructuralListFieldSyntax.field_rename w D z P (old 2)) (HornBinderRules.under_body 2 hzero E))
    (HornBinderRules.under_body 2 (SyntaxNumerals.range hZ k w i hw hi) E)
    (of_eq (StructuralListFieldSyntax.field_rename w S i V (old 2)) (HornBinderRules.under_body 2 hvalue E))
    he (of_eq (substituted_rename w D S a f z T q Y (old 2)) (HornBinderRules.under_body 2 hq E))
  exact of_eq (ForcingMemberGuardOpening.result_rename w P V Y (old 2)).symm out

/-- Read the actual carrier from the shared table. The condition overwrite
acts at index k+1 and preserves the carrier at k. -/
theorem compare_member {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y Base j Q i V M : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hp : Derives Gamma (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hh : Derives Gamma (SyntaxMixedImageHead.head w alpha f own head))
    (hc : Derives Gamma (ForcingGuardCode.compiled false Reln w alpha f head q))
    (hq : Derives Gamma (substituted w (u 7) (v 9) alpha f z B q Y))
    (hf : Derives Gamma (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Gamma (SyntaxNumeralSyntax.numeral (k+1) j))
    (hi : Derives Gamma (SyntaxNumeralSyntax.numeral k i))
    (hr : Derives Gamma (ForcingReflexiveImages.replacement w f z B Base j Q (v 9)))
    (hV : Derives Gamma (StructuralListFieldSyntax.field w Base i V))
    (hm : Derives Gamma (ForcingMemberGuardOpening.result w t V M)) :
    Derives Gamma (.equal Y M) := by
  have src := Derives.conjL hp
  have hw := Derives.conjL src
  have hz := Derives.conjL (.conjR src)
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))
  have images := Derives.conjL (.conjR hp)
  have lists := SyntaxMixedImageCodePairs.term_lists w (v 6) (v 7) a f z B (v 8) (v 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have cons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hp)))))))
  have zero := StructuralListFieldCons.zero_value hZ w t (v 8) (u 7) z hw (SyntaxTerms.range hZ w z B t hw ht)
    (.conjL (.conjL (.conjR (.conjR (.conjL lists))))) cons hz
  have oz := OmegaUniversal.empty_unique own z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hz
  have head0 := SyntaxVariableImagePoint.code_subst_index true w own head z oz (.conjL (.conjR hh))
  have carrier := ForcingPreorderGuardTables.carrier_field hZ w f z B Base j Q (v 9) i V hf hj hi hr hV
  exact ForcingPreorderMember.same_result hZ w t V Y M hw
    (member_query hZ Reln w z (u 7) (v 9) alpha f B head t i V q Y hw hz head0 zero hi carrier hc hq) hm

private structure OrderInputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hw : Derives Γ (omega w)
  hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)
  h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)
  h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)
  h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)
  hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j)
  hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D)
  hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 1) Sg)
  hs : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z T S)
  hp0 : Derives Γ (SyntaxTermSyntax.term w z T (P 0))
  hp1 : Derives Γ (SyntaxTermSyntax.term w z T (P 1))

private theorem OrderInputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {w z A1 A2 A3 f T C B S Refl Pre j Sg : Fin m}
    {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m}
    {U F P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : OrderInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D) (E : Formula (m+l)) :
    OrderInputs (Context.add E (raisedContext l Γ)) test R
      (old l w) (old l z) (old l A1) (old l A2) (old l A3) (old l f) (old l T) (old l C)
      (old l B) (old l S) (old l Refl) (old l Pre) (old l j) (old l Sg)
      (fun i => old l (v i)) (fun i => old l (Gb i)) (fun i => old l (H i))
      (fun i => old l (U i)) (fun i => old l (F i)) (fun i => old l (P i))
      (fun i => old l (N i)) (fun i => old l (D i)) := by
  exact ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (omega_rename w (old l)) (HornBinderRules.under_body l h.hw E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 0 z (old l)) (HornBinderRules.under_body l h.hz E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 (old l)) (HornBinderRules.under_body l h.h1 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 (old l)) (HornBinderRules.under_body l h.h2 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename 3 A3 (old l)) (HornBinderRules.under_body l h.h3 E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f (old l)) (HornBinderRules.under_body l h.hf E),
    of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j (old l)) (HornBinderRules.under_body l h.hj E),
    of_eq (ForcingPreorderLeaves.data_rename test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D (old l)) (HornBinderRules.under_body l h.hd
      E),
    of_eq (ForcingReflexiveImages.replacement_rename w f z T S j (P 1) Sg (old l)) (HornBinderRules.under_body l h.hr E),
    of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z T S (old l)) (HornBinderRules.under_body l h.hs E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P 0) (old l)) (HornBinderRules.under_body l h.hp0 E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P 1) (old l)) (HornBinderRules.under_body l h.hp1 E)⟩

private theorem order_at_direct {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg g G X I J M W Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (E : Fin 4 → Fin m)
    (h : OrderInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hSource : Derives Γ (ForcingRelationSource.data R 0 w z g A3 f (v 13) G X E))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (P 0) (P 1) I J M W))
    (hDirect : Derives Γ (ForcingGuardOpening.direct w z f T (P 0) Sg g G Y)) :
    Derives Γ (.equal (H 3) Y) := by
  let V := (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => (P 0).castSucc) (Fin.last m)).conj
    (substituted w.castSucc (Fin.last m) Sg.castSucc g.castSucc f.castSucc z.castSucc T.castSucc G.castSucc Y.castSucc)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hDirect
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have h1 := h.in_body V
  have hSource1 := of_eq (ForcingRelationSource.data_rename R 0 w z g A3 f (v 13) G X E Fin.castSucc) (under hSource V)
  have hImages1 := of_eq (ForcingRelationImages.data_rename k w f z T S (P 0) (P 1) I J M W Fin.castSucc) (under hImages V)
  have hJ := Derives.conjL (Derives.conjR hImages1)
  have heq := SyntaxNumerals.unique h1.zf (k+1) j.castSucc J.castSucc h1.hj hJ
  have hr := ForcingPreorderGuardTables.replacement_index w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc (P 1).castSucc
    Sg.castSucc J.castSucc heq h1.hr
  exact ForcingPreorderLeaves.relation_from_data h1.zf test R 0 w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc T.castSucc
    C.castSucc B.castSucc S.castSucc Refl.castSucc Pre.castSucc
    g.castSucc G.castSucc X.castSucc I.castSucc J.castSucc M.castSucc W.castSucc (Fin.last m) Sg.castSucc Y.castSucc
    (fun i => (v i).castSucc) (fun i => (Gb i).castSucc) (fun i => (H i).castSucc)
    (fun i => (U i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc)
    (fun i => (N i).castSucc) (fun i => (D i).castSucc) (fun i => (E i).castSucc)
    h1.hw h1.hz h1.h1 h1.h2 h1.hf h1.hd hSource1 hImages1 (.conjL hV) hr (.conjR hV)

private theorem order_at_guard_data {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2))
    (w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (g : Fin 4 → Fin m)
    (h : OrderInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hg : Derives Γ (ForcingGuardOpening.data true R w z f T (P 0) Sg a head q Y g)) :
    Derives Γ (.equal (H 3) Y) := by
  have hSrc := ForcingRelationSource.from_matrix h.zf R 0 w z A1 A2 A3 f a head q v g
    h.hw h.hz h.h3 h.hf (.conjL h.hd) (.conjL hg)
  let E := ForcingRelationSource.body R 0 w z (g 0) A3 f (v 13) (g 1)
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ hSrc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := h.in_body E
  have hd5 := of_eq (ForcingGuardOpening.direct_rename w z f T (P 0) Sg (g 0) (g 1) Y (old 5)) (HornBinderRules.under_body 5 (.conjR hg) E)
  have hTables := ForcingRelationImages.produce h5.zf k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P 1)) h5.hw h5.hs
    h5.hp0 h5.hp1
  let L := ForcingRelationImages.body k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P 1))
  let Ξ := Context.add L (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 L _ hTables
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have h9 := h5.in_body L
  have hd9 := of_eq (ForcingGuardOpening.direct_rename (old 5 w) (old 5 z) (old 5 f) (old 5 T) (old 5 (P 0)) (old 5 Sg) (old 5 (g 0)) (old 5 (g
    1)) (old 5 Y) (old 4)) (HornBinderRules.under_body 4 hd5 L)
  have hs9 : Derives Ξ (ForcingRelationSource.data R 0 (old 9 w) (old 9 z) (old 9 (g 0)) (old 9 A3) (old 9 f) (old 9 (v 13)) (old 9 (g 1))
      (old 4 (slot 5 0)) (fun i => old 4 (slot 5 i.succ))) :=
    of_eq (by simp only [E, ForcingRelationSource.body, ForcingRelationSource.data_rename]; rfl) (HornBinderRules.under_body 4 hE L)
  exact order_at_direct test R (old 9 w) (old 9 z) (old 9 A1) (old 9 A2) (old 9 A3) (old 9 f) (old 9 T) (old 9 C) (old 9 B) (old 9 S) (old 9 Refl)
    (old 9 Pre) (old 9 j) (old 9 Sg)
    (old 9 (g 0)) (old 9 (g 1)) (old 4 (slot 5 0)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 9 Y)
    (fun i => old 9 (v i)) (fun i => old 9 (Gb i)) (fun i => old 9 (H i))
    (fun i => old 9 (U i)) (fun i => old 9 (F i)) (fun i => old 9 (P i))
    (fun i => old 9 (N i)) (fun i => old 9 (D i)) (fun i => old 4 (slot 5 i.succ))
    h9 hs9 hL hd9

/-- Compare the actual order guard with the first relation leaf, R(r,q). -/
theorem compare_order {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (k+2)) (w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P 1) Sg))
    (hg : Derives Γ (ForcingGuardOpening.result true R w z f T (P 0) Sg a head q Y)) :
    Derives Γ (.equal Y (H 3)) := by
  have row := Derives.conjL (.conjL (.conjR hd))
  have hParent := Derives.conjL (.conjR (.conjR hd))
  have hs := Derives.conjR (.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hParent))
  have hp0 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 0) (F 0) (U 1) (.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR row))))))))))
  have hp1 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 1) (F 1) (U 2) (.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR row))))))))))))
  have h : OrderInputs Γ test R w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D :=
    ⟨hZ,hw,hz,hA1,hA2,hA3,hf,hj,hd,hr,hs,hp0,hp1⟩
  let E := ForcingGuardOpening.body true R w z f T (P 0) Sg a head q Y
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hg
  have he : Derives Δ E := .hyp (Or.inl rfl)
  exact eq_symm (order_at_guard_data test R (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3)
    (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 j)
    (old 4 Sg) (old 4 a) (old 4 head) (old 4 q) (old 4 Y)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i))
    (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i))
    (fun i => old 4 (N i)) (fun i => old 4 (D i)) (slot 4) (h.in_body E) he)

/-- Compare the actual existential tail with the canonical execution on the
same prefixed bound table. The source constructors and new query come from
the original compiler and the two implications of its opened parent. -/
theorem compare_existential_tail {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B t R S j N n x Parent Base i p q Old Tail : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (r : Fin 4 → Fin m)
    (hp : Derives Γ (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hc : Derives Γ (ForcingExistCode.data Reln Dom w a alpha beta gamma f j N n cv))
    (hs : Derives Γ (ForcingExistCode.shellData w a alpha beta gamma f
      (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) n sv))
    (hr : Derives Γ (data w (u 7) (v 9) alpha f z B (cv 2) (cv 3) (sv 4) (sv 5) (u 8) r))
    (hBeta : Derives Γ (successor beta alpha)) (hGamma : Derives Γ (successor gamma beta))
    (hChild : Derives Γ (FormulaCodeSyntax.formulaCode w N alpha f))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hOld : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j p Old))
    (hNew : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j q (v 9)))
    (hOldQuery : Derives Γ (substituted w (u 7) Old alpha f z B (sv 4) Tail)) :
    Derives Γ (.equal (r 3) Tail) := by
  let s := ForcingExistTailOpening.shellCodes (cv 4) (cv 5) (cv 6) (cv 7) sv
  have src := Derives.conjL hp
  have hw := Derives.conjL src
  have hz := Derives.conjL (.conjR src)
  have images := Derives.conjL (.conjR hp)
  have lists := SyntaxMixedImageCodePairs.term_lists w (v 6) (v 7) a f z B (v 8) (v 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have head := Derives.conjL hc
  have e := OmegaUniversal.empty_unique (cv 0) z (ZFContext.arithmetic hZ).base.extensionality (.conjL head) hz
  have hHead0 := SyntaxVariableImagePoint.code_subst_index true w (cv 0) (cv 1) z e (.conjL (.conjR head))
  have hSource : Derives Γ (ForcingExistTailOpening.source w s) :=
    .conjI (.conjL (.conjL (.conjR (.conjR (.conjR (.conjR hs))))))
      (.conjI (.conjL (.conjL (.conjR (.conjR (.conjR hs)))))
        (.conjI (.conjL (.conjL (.conjR (.conjR hs))))
          (.conjI (.conjL (.conjL (.conjR hs)))
            ((.conjL (.conjL hs))))))
  have hInput : Derives Γ (ForcingExistTailComparison.rawInput Reln Dom w z a alpha beta gamma f B
      (v 8) (u 7) t Base i j p q (cv 1) N Old Tail (v 9) (r 3) s) := by
    refine .conjI hw ?_
    refine .conjI hz ?_
    refine .conjI (.conjL (.conjR (.conjR src))) ?_
    refine .conjI hBeta ?_
    refine .conjI hGamma ?_
    refine .conjI (.conjL lists) ?_
    refine .conjI (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))) ?_
    refine .conjI (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hp)))))))) ?_
    refine .conjI hChild ?_
    refine .conjI hOld ?_
    refine .conjI hNew ?_
    refine .conjI hSource ?_
    refine .conjI hOldQuery ?_
    refine .conjI (.conjR (.conjR (.conjR hr))) ?_
    refine .conjI hi ?_
    refine .conjI hj ?_
    refine .conjI hf ?_
    refine .conjI hHead0 ?_
    refine .conjI (.conjL (.conjR (.conjR (.conjR hc)))) ?_
    refine .conjI (.conjL (.conjR (.conjR (.conjR (.conjR hc))))) ?_
    refine .conjI (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hc)))))) ?_
    exact .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hc))))))
  exact eq_symm (ForcingExistTailComparison.from_queries hZ Reln Dom w z a alpha beta gamma f B
    (v 8) (u 7) t Base i j p q (cv 1) N Old Tail (v 9) (r 3) s hInput)

private theorem compare_member_from_row {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent A1 A2 A3 C T Base Refl Pre i j own head sm Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hp : Derives Γ (ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R S n x Parent v u))
    (hh : Derives Γ (SyntaxMixedImageHead.head w alpha f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w alpha f head sm))
    (hq : Derives Γ (substituted w (u 7) (v 9) alpha f z B sm Y))
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hd : Derives Γ (ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B C T Base Refl Pre raw Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j (P 1) (v 9))) :
    Derives Γ (.equal Y (H 0)) := by
  have hw := Derives.conjL (.conjL hp)
  have field := StructuralListFieldValues.exists_value hZ w Base i hw (SyntaxNumerals.range hZ k w i hw hi)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc Base.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) field
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hp1 := of_eq (ForcingFreshParentOpening.data_rename w z a f alpha b A B (P 0) R S n x Parent v u
    Fin.castSucc) (under hp E)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w alpha f own head Fin.castSucc) (under hh E)
  have hc1 := of_eq (ForcingGuardCode.compiled_rename false Reln w alpha f head sm Fin.castSucc) (under hc E)
  have hq1 := of_eq (substituted_rename w (u 7) (v 9) alpha f z B sm Y Fin.castSucc) (under hq E)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under hz E)
  have h11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under h1 E)
  have h21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under h2 E)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f Fin.castSucc) (under hf E)
  have hj1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+1) j Fin.castSucc) (under hj E)
  have hi1 := of_eq (SyntaxNumeralSyntax.numeral_rename k i Fin.castSucc) (under hi E)
  have hd1 := of_eq (ForcingPreorderLeaves.data_rename test Reln w z A1 A2 A3 f B C T Base Refl Pre
    raw Gb H U F P N D Fin.castSucc) (under hd E)
  have hr1 := of_eq (ForcingReflexiveImages.replacement_rename w f z B Base j (P 1) (v 9) Fin.castSucc)
    (under hr E)
  have member := ForcingPreorderMember.raw_from_data hZ1 test Reln 0
    w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc B.castSucc C.castSucc T.castSucc Base.castSucc Refl.castSucc Pre.castSucc
      i.castSucc (Fin.last m)
    (fun i => (raw i).castSucc) (fun i => (Gb i).castSucc) (fun i => (H i).castSucc)
    (fun i => (U i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc) (fun i => (N i).castSucc) (fun i => (D i).castSucc)
    hw1 hz1 h11 h21 hi1 hd1 (.conjR hE)
  exact compare_member hZ1 Reln w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc A.castSucc B.castSucc (P 0).castSucc
    R.castSucc S.castSucc n.castSucc x.castSucc Parent.castSucc
    own.castSucc head.castSucc sm.castSucc Y.castSucc Base.castSucc j.castSucc (P 1).castSucc i.castSucc
    (Fin.last m) (H 0).castSucc (fun i => (v i).castSucc) (fun i => (u i).castSucc) hp1 hh1 hc1 hq1 hf1 hj1 hi1 hr1 (.conjR hE) member

/-- The original compiler fields, the shared preorder row, and the canonical
nested proof built from the old tail query. The new guard and tail results are
obtained by opening the actual parent in the overwritten table. -/
def existentialRootInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R S n x Parent v u).conj
    ((ForcingExistCode.data Reln Dom w a alpha beta gamma f j N n cv).conj
    ((ForcingExistCode.shellData w a alpha beta gamma f (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) n sv).conj
    ((successor beta alpha).conj
    ((successor gamma beta).conj
    ((FormulaCodeSyntax.formulaCode w N alpha f).conj
    ((SyntaxNumeralSyntax.numeral 0 z).conj
    ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj
    ((SyntaxNumeralSyntax.numeral 3 A3).conj
    ((SyntaxNumeralSyntax.numeral (k+2) f).conj
    ((SyntaxNumeralSyntax.numeral (k+1) j).conj
    ((SyntaxNumeralSyntax.numeral k i).conj
    ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B C T Base Refl Pre raw Gb H U F P N0 D).conj
    ((ForcingReflexiveImages.replacement w f z B Base j (P 2) Old).conj
    ((ForcingReflexiveImages.replacement w f z B Base j (P 1) (v 9)).conj
    ((substituted w (u 7) Old alpha f z B (sv 4) Tail).conj
    ((ForcingNestedGuardProof.data test w z b A B G W (H 0) (H 3) Tail I K J))))))))))))))))))

theorem existentialRootInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (rho : Fin m → Fin l) :
    (existentialRootInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J v u cv
      sv raw Gb H U F P N0 D).rename rho =
      existentialRootInput test Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A) (rho B) (rho R) (rho
        S) (rho j) (rho N) (rho n) (rho x) (rho Parent) (rho A1) (rho A2) (rho A3) (rho C) (rho T) (rho Base) (rho Refl) (rho Pre) (rho i) (rho
        Old) (rho Tail) (rho G) (rho W) (rho I) (rho K) (rho J)
        (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (cv i)) (fun i => rho (sv i)) (fun i => rho (raw i)) (fun i => rho (Gb i)) (fun i
          => rho (H i)) (fun i => rho (U i)) (fun i => rho (F i)) (fun i => rho (P i)) (fun i => rho (N0 i)) (fun i => rho (D i)) := by
  simp only [existentialRootInput, Formula.rename, ForcingFreshParentOpening.data_rename,
    ForcingExistCode.data_rename, ForcingExistCode.shellData_rename, successor_rename,
    FormulaCodeSyntax.formulaCode_rename, SyntaxNumeralSyntax.numeral_rename,
    ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename,
    substituted_rename, ForcingNestedGuardProof.data_rename]

private theorem existential_root_at_outputs {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (r : Fin 4 → Fin m)
    (hi : Derives Γ (existentialRootInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G
      W I K J v u cv sv raw Gb H U F P N0 D))
    (hr : Derives Γ (guardData Reln w (u 7) (v 9) alpha f z B (P 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (u 8) r)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  have parent := Derives.conjL hi
  have rest := Derives.conjR hi
  have compiler := Derives.conjL rest
  have rest := Derives.conjR rest
  have shell := Derives.conjL rest
  have rest := Derives.conjR rest
  have hBeta := Derives.conjL rest
  have rest := Derives.conjR rest
  have hGamma := Derives.conjL rest
  have rest := Derives.conjR rest
  have child := Derives.conjL rest
  have rest := Derives.conjR rest
  have zero := Derives.conjL rest
  have rest := Derives.conjR rest
  have one := Derives.conjL rest
  have rest := Derives.conjR rest
  have two := Derives.conjL rest
  have rest := Derives.conjR rest
  have three := Derives.conjL rest
  have rest := Derives.conjR rest
  have free := Derives.conjL rest
  have rest := Derives.conjR rest
  have condition := Derives.conjL rest
  have rest := Derives.conjR rest
  have carrier := Derives.conjL rest
  have rest := Derives.conjR rest
  have row := Derives.conjL rest
  have rest := Derives.conjR rest
  have oldTable := Derives.conjL rest
  have rest := Derives.conjR rest
  have newTable := Derives.conjL rest
  have rest := Derives.conjR rest
  have tail := Derives.conjL rest
  have nested := Derives.conjR rest
  have head := head_at_parent hZ w z a f alpha b A B (P 0) R S n x Parent gamma
    (cv 0) (cv 1) (.conjL parent) (.conjL compiler)
  have rawOutputs := Derives.conjL hr
  have member := compare_member_from_row hZ test Reln w z a f alpha b A B R S n x Parent
    A1 A2 A3 C T Base Refl Pre i j (cv 0) (cv 1) (cv 2) (r 1)
    v u raw Gb H U F P N0 D parent head (.conjL (.conjR compiler)) (.conjL (.conjR (.conjL rawOutputs)))
    zero one two free condition carrier row newTable
  have order := compare_order hZ test Reln w z A1 A2 A3 f B C T Base Refl Pre j (v 9) alpha (cv 1)
    (cv 3) (r 2) raw Gb H U F P N0 D (.conjL (.conjL parent))
    zero one two three free condition row newTable (.conjR (.conjR hr))
  have tailEq := compare_existential_tail hZ Reln Dom w z a f alpha beta gamma b A B (P 0) R S j
    N n x Parent Base i (P 2) (P 1) Old Tail v u cv sv r parent compiler shell rawOutputs
    hBeta hGamma child carrier condition free oldTable newTable tail
  exact consume_matched hZ test w z a f alpha b A B (P 0) R S n x Parent
    (cv 2) (cv 3) (sv 4) (sv 5) G W (H 0) (H 3) Tail I K J
    v u r parent rawOutputs nested member order tailEq

/-- Use the original existential compiler's actual fresh outputs to
discharge all three leaf comparisons before consuming the Root proof. -/
theorem consume_existential_root {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hi : Derives Γ (existentialRootInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G
      W I K J v u cv sv raw Gb H U F P N0 D)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  have record := existential_at_records hZ Reln Dom w z a f alpha beta gamma b A B (P 0) R S j
    N n x Parent v u cv sv (.conjL hi) (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi)))
  let E := guardData Reln (old 4 w) (old 4 (u 7)) (old 4 (v 9)) (old 4 alpha) (old 4 f) (old 4 z) (old 4 B)
    (old 4 (P 0)) (old 4 (cv 1)) (old 4 (cv 2)) (old 4 (cv 3)) (old 4 (sv 4)) (old 4 (sv 5)) (old 4 (u 8)) (slot 4)
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (.conjR (.conjR (.conjR record)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 := of_eq (existentialRootInput_rename test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old
    Tail G W I K J v u cv sv raw Gb H U F P N0 D (old 4))
    (HornBinderRules.under_body 4 hi E)
  apply of_eq (InternalProofBackground.implication_rename test w z b G Parent (old 4)).symm
  exact existential_root_at_outputs (HornBinderRules.zf_body 4 hZ E) test Reln Dom (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 alpha) (old 4
    beta) (old 4 gamma) (old 4 b) (old 4 A) (old 4 B) (old 4 R) (old 4 S) (old 4 j) (old 4 N) (old 4 n) (old 4 x) (old 4 Parent) (old 4 A1) (old 4
    A2) (old 4 A3) (old 4 C) (old 4 T) (old 4 Base) (old 4 Refl) (old 4 Pre) (old 4 i) (old 4 Old) (old 4 Tail) (old 4 G) (old 4 W) (old 4 I) (old
    4 K) (old 4 J)
    (fun i => old 4 (v i)) (fun i => old 4 (u i)) (fun i => old 4 (cv i)) (fun i => old 4 (sv i)) (fun i => old 4 (raw i)) (fun i => old 4 (Gb i))
      (fun i => old 4 (H i)) (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N0 i)) (fun i => old 4 (D i))
      (slot 4) hi4 hE

def existentialRootSentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((existentialRootInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J v u cv sv
    raw Gb H U F P N0 D).imp
    (InternalProofBackground.implication test w z b G Parent)).close

theorem existential_root_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Old Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (existentialRootSentence test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i
        Old Tail G W I K J v u cv sv raw Gb H U F P N0 D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact consume_existential_root (ZFContext.add (ZFContext.source_ZF m) _) test Reln Dom w z a f alpha beta gamma b A B R S j N n x Parent A1 A2
    A3 C T Base Refl Pre i Old Tail G W I K J v u cv sv raw Gb H U F P N0 D
    (.hyp (Or.inl rfl))


/-- Data at the actual fresh parent and the shared preorder row. The
canonical tail uses the original child at the fresh condition. -/
def negativeRootInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R S n x Parent v u).conj
    ((ForcingNegCode.compiled Reln w a alpha f j N n).conj
      ((SyntaxNumeralSyntax.numeral 0 z).conj
        ((SyntaxNumeralSyntax.numeral 1 A1).conj
          ((SyntaxNumeralSyntax.numeral 2 A2).conj
            ((SyntaxNumeralSyntax.numeral 3 A3).conj
              ((SyntaxNumeralSyntax.numeral (k+2) f).conj
                ((SyntaxNumeralSyntax.numeral (k+1) j).conj
                  ((SyntaxNumeralSyntax.numeral k i).conj
                    ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B C T Base Refl Pre raw Gb H U F P N0 D).conj
                      ((ForcingReflexiveImages.replacement w f z B Base j (P 0) Sel).conj
                        ((ForcingReflexiveImages.replacement w f z B Base j (P 1) (v 9)).conj
                          ((substituted w (v 8) Sel a f z B N Operand).conj
                            ((SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 FalseCode).conj
                              ((binaryCode 2 w Operand FalseCode Tail).conj
                                ((ForcingNestedGuardProof.data test w z b A B G W (H 0) (H 3) Tail I K J))))))))))))))))

theorem negativeRootInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (rho : Fin m → Fin l) :
    (negativeRootInput test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J v u raw
      Gb H U F P N0 D).rename rho =
      negativeRootInput test Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho R) (rho S) (rho j) (rho N) (rho n) (rho
        x) (rho Parent) (rho A1) (rho A2) (rho A3) (rho C) (rho T) (rho Base) (rho Refl) (rho Pre) (rho i) (rho Sel) (rho Operand) (rho FalseCode)
        (rho Tail) (rho G) (rho W) (rho I) (rho K) (rho J) (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (raw i)) (fun i => rho (Gb i))
        (fun i => rho (H i)) (fun i => rho (U i)) (fun i => rho (F i)) (fun i => rho (P i)) (fun i => rho (N0 i)) (fun i => rho (D i)) := by
  simp only [negativeRootInput, Formula.rename, ForcingFreshParentOpening.data_rename, ForcingNegCode.compiled_rename,
    SyntaxNumeralSyntax.numeral_rename, ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename,
    substituted_rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map,
    binaryCode_rename, ForcingNestedGuardProof.data_rename]

private theorem negative_root_at_outputs {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (cv : Fin 5 → Fin m) (sv r : Fin 4 → Fin m)
    (hi : Derives Γ (negativeRootInput test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G
      W I K J v u raw Gb H U F P N0 D))
    (records : Derives Γ (negativeRecord Reln w z a f alpha b A B (P 0) R S j N n x Parent v u cv sv))
    (hr : Derives Γ (guardData Reln w (u 7) (v 9) alpha f z B (P 0) (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (u 8) r)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  have parent := Derives.conjL hi
  have rest := Derives.conjR hi
  have rest := Derives.conjR rest
  have zero := Derives.conjL rest
  have rest := Derives.conjR rest
  have one := Derives.conjL rest
  have rest := Derives.conjR rest
  have two := Derives.conjL rest
  have rest := Derives.conjR rest
  have three := Derives.conjL rest
  have rest := Derives.conjR rest
  have free := Derives.conjL rest
  have rest := Derives.conjR rest
  have condition := Derives.conjL rest
  have rest := Derives.conjR rest
  have carrier := Derives.conjL rest
  have rest := Derives.conjR rest
  have row := Derives.conjL rest
  have rest := Derives.conjR rest
  have selTable := Derives.conjL rest
  have rest := Derives.conjR rest
  have newTable := Derives.conjL rest
  have rest := Derives.conjR rest
  have operand := Derives.conjL rest
  have rest := Derives.conjR rest
  have falseCode := Derives.conjL rest
  have rest := Derives.conjR rest
  have tailCode := Derives.conjL rest
  have nested := Derives.conjR rest
  have hc := Derives.conjL (.conjR records)
  have hs := Derives.conjL (.conjR (.conjR records))
  have rawOutputs := Derives.conjL hr
  have member := compare_member_from_row hZ test Reln w z a f alpha b A B R S n x Parent
    A1 A2 A3 C T Base Refl Pre i j (cv 0) (cv 1) (cv 3) (r 1) v u raw Gb H U F P N0 D
    parent (.conjL hc) (.conjL (.conjR (.conjR hc))) (.conjL (.conjR (.conjL rawOutputs)))
    zero one two free condition carrier row newTable
  have src := Derives.conjL parent
  have hw := Derives.conjL src
  have order := compare_order hZ test Reln w z A1 A2 A3 f B C T Base Refl Pre j (v 9) alpha
    (cv 1) (cv 4) (r 2) raw Gb H U F P N0 D hw zero one two three free condition row newTable
    (.conjR (.conjR hr))
  have hTerm := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))
  have hCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR parent)))))))
  have tailEq := ForcingRawNegTail.compare hZ w z a alpha f B (v 8) (u 7) (v 9) Base j
    (P 0) (P 1) Sel N (cv 2) (sv 0) (sv 1) (r 3) Operand FalseCode Tail hw (.conjL (.conjR src))
    hTerm hCons newTable selTable (.conjL (.conjR hc)) (.conjL (.conjL (.conjR hs))) (.conjL (.conjL hs))
    (.conjR (.conjR (.conjR rawOutputs))) operand falseCode tailCode
  exact consume_matched hZ test w z a f alpha b A B (P 0) R S n x Parent
    (cv 3) (cv 4) (sv 1) (sv 2) G W (H 0) (H 3) Tail I K J
    v u r parent rawOutputs nested member order tailEq

private theorem negative_root_at_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m)
    (hi : Derives Γ (negativeRootInput test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G
      W I K J v u raw Gb H U F P N0 D))
    (records : Derives Γ (negativeRecord Reln w z a f alpha b A B (P 0) R S j N n x Parent v u cv sv)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  let E := guardData Reln (old 4 w) (old 4 (u 7)) (old 4 (v 9)) (old 4 alpha) (old 4 f) (old 4 z) (old 4 B)
    (old 4 (P 0)) (old 4 (cv 1)) (old 4 (cv 3)) (old 4 (cv 4)) (old 4 (sv 1)) (old 4 (sv 2)) (old 4 (u 8)) (slot 4)
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ (.conjR (.conjR (.conjR records)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 := of_eq (negativeRootInput_rename test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode
    Tail G W I K J v u raw Gb H U F P N0 D (old 4))
    (HornBinderRules.under_body 4 hi E)
  have rec4 := of_eq (negativeRecord_rename Reln w z a f alpha b A B (P 0) R S j N n x Parent v u cv sv (old 4))
    (HornBinderRules.under_body 4 records E)
  apply of_eq (InternalProofBackground.implication_rename test w z b G Parent (old 4)).symm
  exact negative_root_at_outputs (HornBinderRules.zf_body 4 hZ E) test Reln (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 alpha) (old 4 b) (old 4
    A) (old 4 B) (old 4 R) (old 4 S) (old 4 j) (old 4 N) (old 4 n) (old 4 x) (old 4 Parent) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 C) (old 4 T)
    (old 4 Base) (old 4 Refl) (old 4 Pre) (old 4 i) (old 4 Sel) (old 4 Operand) (old 4 FalseCode) (old 4 Tail) (old 4 G) (old 4 W) (old 4 I) (old
    4 K) (old 4 J) (fun i => old 4 (v i)) (fun i => old 4 (u i)) (fun i => old 4 (raw i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i)) (fun i =>
    old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i)) (fun i => old 4 (N0 i)) (fun i => old 4 (D i))
    (fun i => old 4 (cv i)) (fun i => old 4 (sv i)) (slot 4) hi4 rec4 hE

/-- The actual negative compiler supplies all source and output witnesses.
Each of the three comparisons is proved at those same witnesses. -/
theorem consume_negative_root {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hi : Derives Γ (negativeRootInput test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G
      W I K J v u raw Gb H U F P N0 D)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  have records := from_negative hZ Reln w z a f alpha b A B (P 0) R S j N n x Parent v u (.conjL hi) (.conjL (.conjR hi))
  let E := negativeAt Reln (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 alpha) (old 5 b) (old 5 A) (old 5 B) (old 5 (P 0)) (old 5 R) (old 5 S)
    (old 5 j) (old 5 N) (old 5 n) (old 5 x) (old 5 Parent)
    (fun i => old 5 (v i)) (fun i => old 5 (u i)) (slot 5)
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ records
  apply of_eq (InternalProofBackground.implication_rename test w z b G Parent (old 5)).symm
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let L := negativeRecord Reln ((old 4 ∘ old 5) w) ((old 4 ∘ old 5) z) ((old 4 ∘ old 5) a) ((old 4 ∘ old 5) f) ((old 4 ∘ old 5) alpha) ((old 4 ∘
    old 5) b) ((old 4 ∘ old 5) A) ((old 4 ∘ old 5) B) ((old 4 ∘ old 5) (P 0)) ((old 4 ∘ old 5) R) ((old 4 ∘ old 5) S) ((old 4 ∘ old 5) j) ((old 4
    ∘ old 5) N) ((old 4 ∘ old 5) n) ((old 4 ∘ old 5) x) ((old 4 ∘ old 5) Parent)
    (fun i => old 4 (old 5 (v i))) (fun i => old 4 (old 5 (u i))) (fun i => old 4 (slot 5 i)) (slot 4)
  let Ξ := Context.add L (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 L _ hE
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hi5 := of_eq (negativeRootInput_rename test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode
    Tail G W I K J v u raw Gb H U F P N0 D (old 5)) (HornBinderRules.under_body 5 hi E)
  have hi9 := of_eq (negativeRootInput_rename test Reln (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 alpha) (old 5 b) (old 5 A) (old 5 B) (old 5
    R) (old 5 S) (old 5 j) (old 5 N) (old 5 n) (old 5 x) (old 5 Parent) (old 5 A1) (old 5 A2) (old 5 A3) (old 5 C) (old 5 T) (old 5 Base) (old 5
    Refl) (old 5 Pre) (old 5 i) (old 5 Sel) (old 5 Operand) (old 5 FalseCode) (old 5 Tail) (old 5 G) (old 5 W) (old 5 I) (old 5 K) (old 5 J) (fun
    i => old 5 (v i)) (fun i => old 5 (u i)) (fun i => old 5 (raw i)) (fun i => old 5 (Gb i)) (fun i => old 5 (H i)) (fun i => old 5 (U i)) (fun i
    => old 5 (F i)) (fun i => old 5 (P i)) (fun i => old 5 (N0 i)) (fun i => old 5 (D i)) (old 4)) (HornBinderRules.under_body 4 hi5 L)
  apply of_eq (InternalProofBackground.implication_rename test (old 5 w) (old 5 z) (old 5 b)
    (old 5 G) (old 5 Parent) (old 4)).symm
  exact negative_root_at_records (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 5 hZ E) L)
    test Reln ((old 4 ∘ old 5) w) ((old 4 ∘ old 5) z) ((old 4 ∘ old 5) a) ((old 4 ∘ old 5) f) ((old 4 ∘ old 5) alpha) ((old 4 ∘ old 5) b) ((old 4
      ∘ old 5) A) ((old 4 ∘ old 5) B) ((old 4 ∘ old 5) R) ((old 4 ∘ old 5) S) ((old 4 ∘ old 5) j) ((old 4 ∘ old 5) N) ((old 4 ∘ old 5) n) ((old 4
      ∘ old 5) x) ((old 4 ∘ old 5) Parent) ((old 4 ∘ old 5) A1) ((old 4 ∘ old 5) A2) ((old 4 ∘ old 5) A3) ((old 4 ∘ old 5) C) ((old 4 ∘ old 5) T)
      ((old 4 ∘ old 5) Base) ((old 4 ∘ old 5) Refl) ((old 4 ∘ old 5) Pre) ((old 4 ∘ old 5) i) ((old 4 ∘ old 5) Sel) ((old 4 ∘ old 5) Operand)
      ((old 4 ∘ old 5) FalseCode) ((old 4 ∘ old 5) Tail) ((old 4 ∘ old 5) G) ((old 4 ∘ old 5) W) ((old 4 ∘ old 5) I) ((old 4 ∘ old 5) K) ((old 4 ∘
      old 5) J) (fun i => (old 4 ∘ old 5) (v i)) (fun i => (old 4 ∘ old 5) (u i)) (fun i => (old 4 ∘ old 5) (raw i)) (fun i => (old 4 ∘ old 5) (Gb
      i)) (fun i => (old 4 ∘ old 5) (H i)) (fun i => (old 4 ∘ old 5) (U i)) (fun i => (old 4 ∘ old 5) (F i)) (fun i => (old 4 ∘ old 5) (P i)) (fun
      i => (old 4 ∘ old 5) (N0 i)) (fun i => (old 4 ∘ old 5) (D i)) (fun i => old 4 (slot 5 i)) (slot 4) hi9 hL

def negativeRootSentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((negativeRootInput test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J v u raw
    Gb H U F P N0 D).imp
    (InternalProofBackground.implication test w z b G Parent)).close

theorem negative_root_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand FalseCode Tail G W I K J : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (negativeRootSentence test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl Pre i Sel Operand
        FalseCode Tail G W I K J v u raw Gb H U F P N0 D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact consume_negative_root (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z a f alpha b A B R S j N n x Parent A1 A2 A3 C T Base Refl
    Pre i Sel Operand FalseCode Tail G W I K J v u raw Gb H U F P N0 D
    (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingRawModalBody

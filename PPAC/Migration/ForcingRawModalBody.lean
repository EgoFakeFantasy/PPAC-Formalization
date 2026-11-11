import PPAC.Migration.ForcingRawGuardOpening
import PPAC.Migration.ForcingExistTailComparison
import PPAC.Migration.ForcingRawNegTail
import PPAC.Migration.ForcingOldParentInstance
import PPAC.Migration.ForcingConjunctionMono

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
def nestedData {m} (kind : Fin 4) (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingFormulaDiagram.binaryData kind w D S a f z T M I Y (v 1) (v 0)).conj
    (ForcingFormulaDiagram.binaryData kind w D S a f z T O L (v 0) (v 2) (v 3))

theorem nestedData_rename {m l} (kind : Fin 4) (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (nestedData kind w D S a f z T M O L I Y v).rename rho =
      nestedData kind (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) (fun i => rho (v i)) := by
  simp only [nestedData, Formula.rename, ForcingFormulaDiagram.binaryData_rename]

def nestedOutputs {m} (kind : Fin 4) (w D S a f z T M O L I Y : Fin m) : Formula m :=
  existsMany 4 (nestedData kind (old 4 w) (old 4 D) (old 4 S) (old 4 a) (old 4 f) (old 4 z) (old 4 T)
    (old 4 M) (old 4 O) (old 4 L) (old 4 I) (old 4 Y) (slot 4))

theorem nestedOutputs_rename {m l} (kind : Fin 4) (w D S a f z T M O L I Y : Fin m) (rho : Fin m → Fin l) :
    (nestedOutputs kind w D S a f z T M O L I Y).rename rho =
      nestedOutputs kind (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) := by
  simp only [nestedOutputs, existsMany_rename, nestedData_rename, lift_old, lift_slot]

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (SyntaxAtomSyntax.two c d))

theorem nested_from_query {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (kind : Fin 4)
    (w D S a f z T M O L I X Y : Fin m) (hw : Derives Gamma (omega w))
    (houter : Derives Gamma (binaryCode kind w M I X))
    (hinner : Derives Gamma (binaryCode kind w O L I))
    (hq : Derives Gamma (substituted w D S a f z T X Y)) :
    Derives Gamma (nestedOutputs kind w D S a f z T M O L I Y) := by
  let E := ForcingFormulaDiagram.binaryBody kind w D S a f z T M I Y
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _
    (ForcingFormulaDiagram.binary_output hZ kind w D S a f z T X M I Y hw houter hq)
  have he : Derives Delta E := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hinner2 := of_eq (binaryCode_rename kind w O L I (old 2)) (HornBinderRules.under_body 2 hinner E)
  let F := ForcingFormulaDiagram.binaryBody kind (old 2 w) (old 2 D) (old 2 S)
    (old 2 a) (old 2 f) (old 2 z) (old 2 T) (old 2 O) (old 2 L) (slot 2 1)
  let Xi := Context.add F (raisedContext 2 Delta)
  apply HornBinderRules.eliminate_many 2 F _
    (ForcingFormulaDiagram.binary_output (HornBinderRules.zf_body 2 hZ E) kind
      (old 2 w) (old 2 D) (old 2 S) (old 2 a) (old 2 f) (old 2 z) (old 2 T)
      (old 2 I) (old 2 O) (old 2 L) (slot 2 1) hw2 hinner2 (.conjR (.conjR he)))
  have hf : Derives Xi F := .hyp (Or.inl rfl)
  have he4 := of_eq (ForcingFormulaDiagram.binaryData_rename kind (old 2 w) (old 2 D) (old 2 S)
    (old 2 a) (old 2 f) (old 2 z) (old 2 T) (old 2 M) (old 2 I) (old 2 Y)
    (slot 2 0) (slot 2 1) (old 2)) (HornBinderRules.under_body 2 he F)
  have out : Derives Xi (nestedOutputs kind (old 2 (old 2 w)) (old 2 (old 2 D)) (old 2 (old 2 S))
      (old 2 (old 2 a)) (old 2 (old 2 f)) (old 2 (old 2 z)) (old 2 (old 2 T))
      (old 2 (old 2 M)) (old 2 (old 2 O)) (old 2 (old 2 L)) (old 2 (old 2 I)) (old 2 (old 2 Y))) := by
    apply HornBinderRules.intro_many 4 _ (four (old 2 (slot 2 1)) (old 2 (slot 2 0)) (slot 2 0) (slot 2 1))
    exact of_eq (by simp only [nestedData_rename, assign_old, assign_slot]; rfl) (.conjI he4 hf)
  exact of_eq (by simp only [nestedOutputs_rename]) out

def data {m} (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  nestedData 2 w D S a f z T M O L I Y v

theorem data_rename {m l} (w D S a f z T M O L I Y : Fin m) (v : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (data w D S a f z T M O L I Y v).rename rho =
      data (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) (fun i => rho (v i)) :=
  nestedData_rename 2 w D S a f z T M O L I Y v rho

def outputs {m} (w D S a f z T M O L I Y : Fin m) : Formula m :=
  nestedOutputs 2 w D S a f z T M O L I Y

theorem outputs_rename {m l} (w D S a f z T M O L I Y : Fin m) (rho : Fin m → Fin l) :
    (outputs w D S a f z T M O L I Y).rename rho =
      outputs (rho w) (rho D) (rho S) (rho a) (rho f) (rho z) (rho T)
        (rho M) (rho O) (rho L) (rho I) (rho Y) :=
  nestedOutputs_rename 2 w D S a f z T M O L I Y rho

theorem from_query {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w D S a f z T M O L I X Y : Fin m) (hw : Derives Gamma (omega w))
    (houter : Derives Gamma (binaryCode 2 w M I X))
    (hinner : Derives Gamma (binaryCode 2 w O L I))
    (hq : Derives Gamma (substituted w D S a f z T X Y)) :
    Derives Gamma (outputs w D S a f z T M O L I Y) :=
  nested_from_query hZ 2 w D S a f z T M O L I X Y hw houter hinner hq

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

theorem member_atom {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
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

theorem member_query {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma) (Reln : Source.Formula (k+2))
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

private def orderLeaf (oldSide : Bool) : Fin 3 := if oldSide then 2 else 0
private def orderCondition (oldSide : Bool) : Fin 3 := if oldSide then 2 else 1

private theorem order_left {m} (P : Fin 3 → Fin m) (oldSide : Bool) :
    ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex (orderLeaf oldSide)) = P 0 := by
  cases oldSide <;> rfl

private theorem order_right {m} (P : Fin 3 → Fin m) (oldSide : Bool) :
    ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex (orderLeaf oldSide)) =
      P (orderCondition oldSide) := by
  cases oldSide <;> rfl

private structure OrderInputs {k m} (Γ : Context m) (test : Formula 1) (R : Source.Formula (k+2)) (oldSide : Bool)
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
  hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P (orderCondition oldSide)) Sg)
  hs : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f z T S)
  hp0 : Derives Γ (SyntaxTermSyntax.term w z T (P 0))
  hp1 : Derives Γ (SyntaxTermSyntax.term w z T (P (orderCondition oldSide)))

private theorem OrderInputs.in_body {k m l} {Γ : Context m} {test : Formula 1} {R : Source.Formula (k+2)}
    {oldSide : Bool} {w z A1 A2 A3 f T C B S Refl Pre j Sg : Fin m}
    {v : Fin 16 → Fin m} {Gb : Fin 5 → Fin m} {H : Fin 6 → Fin m}
    {U F P : Fin 3 → Fin m} {N : Fin 5 → Fin m} {D : Fin 3 → Fin m}
    (h : OrderInputs Γ test R oldSide w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D) (E : Formula (m+l)) :
    OrderInputs (Context.add E (raisedContext l Γ)) test R oldSide
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
    of_eq (ForcingReflexiveImages.replacement_rename w f z T S j (P (orderCondition oldSide)) Sg (old l)) (HornBinderRules.under_body l h.hr E),
    of_eq (SyntaxMixedImageCodeSyntax.termList_rename w f z T S (old l)) (HornBinderRules.under_body l h.hs E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P 0) (old l)) (HornBinderRules.under_body l h.hp0 E),
    of_eq (SyntaxTermSyntax.term_rename w z T (P (orderCondition oldSide)) (old l)) (HornBinderRules.under_body l h.hp1 E)⟩

private theorem order_at_direct {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2)) (oldSide : Bool)
    (w z A1 A2 A3 f T C B S Refl Pre j Sg g G X I J M W Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (E : Fin 4 → Fin m)
    (h : OrderInputs Γ test R oldSide w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hSource : Derives Γ (ForcingRelationSource.data R (orderLeaf oldSide) w z g A3 f (v (ForcingRelationSource.rawSlot (orderLeaf oldSide))) G X
      E))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (P 0) (P (orderCondition oldSide)) I J M W))
    (hDirect : Derives Γ (ForcingGuardOpening.direct w z f T (P 0) Sg g G Y)) :
    Derives Γ (.equal (H (ForcingPreorderLeaves.relationPosition (orderLeaf oldSide))) Y) := by
  let V := (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => (P 0).castSucc) (Fin.last m)).conj
    (substituted w.castSucc (Fin.last m) Sg.castSucc g.castSucc f.castSucc z.castSucc T.castSucc G.castSucc Y.castSucc)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hDirect
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have h1 := h.in_body V
  have hSource1 := of_eq (ForcingRelationSource.data_rename R (orderLeaf oldSide) w z g A3 f (v (ForcingRelationSource.rawSlot (orderLeaf
    oldSide))) G X E Fin.castSucc) (under hSource V)
  have hImages1 := of_eq (ForcingRelationImages.data_rename k w f z T S (P 0) (P (orderCondition oldSide)) I J M W Fin.castSucc) (under hImages V)
  have hJ := Derives.conjL (Derives.conjR hImages1)
  have heq := SyntaxNumerals.unique h1.zf (k+1) j.castSucc J.castSucc h1.hj hJ
  have hr := ForcingPreorderGuardTables.replacement_index w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc (P (orderCondition
    oldSide)).castSucc
    Sg.castSucc J.castSucc heq h1.hr
  exact ForcingPreorderLeaves.relation_from_data h1.zf test R (orderLeaf oldSide) w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc
    f.castSucc T.castSucc
    C.castSucc B.castSucc S.castSucc Refl.castSucc Pre.castSucc
    g.castSucc G.castSucc X.castSucc I.castSucc J.castSucc M.castSucc W.castSucc (Fin.last m) Sg.castSucc Y.castSucc
    (fun i => (v i).castSucc) (fun i => (Gb i).castSucc) (fun i => (H i).castSucc)
    (fun i => (U i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc)
    (fun i => (N i).castSucc) (fun i => (D i).castSucc) (fun i => (E i).castSucc)
    h1.hw h1.hz h1.h1 h1.h2 h1.hf h1.hd hSource1
    (by rw [order_left, order_right]; exact hImages1)
    (by rw [order_left]; exact .conjL hV)
    (by simpa only [order_right] using hr) (.conjR hV)

private theorem order_at_guard_data {k m} {Γ : Context m} (test : Formula 1) (R : Source.Formula (k+2)) (oldSide : Bool)
    (w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) (g : Fin 4 → Fin m)
    (h : OrderInputs Γ test R oldSide w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D)
    (hg : Derives Γ (ForcingGuardOpening.data true R w z f T (P 0) Sg a head q Y g)) :
    Derives Γ (.equal (H (ForcingPreorderLeaves.relationPosition (orderLeaf oldSide))) Y) := by
  have hSrc := ForcingRelationSource.from_matrix h.zf R (orderLeaf oldSide) w z A1 A2 A3 f a head q v g
    h.hw h.hz h.h3 h.hf (.conjL h.hd) (.conjL hg)
  let E := ForcingRelationSource.body R (orderLeaf oldSide) w z (g 0) A3 f (v (ForcingRelationSource.rawSlot (orderLeaf oldSide))) (g 1)
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ hSrc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := h.in_body E
  have hd5 := of_eq (ForcingGuardOpening.direct_rename w z f T (P 0) Sg (g 0) (g 1) Y (old 5)) (HornBinderRules.under_body 5 (.conjR hg) E)
  have hTables := ForcingRelationImages.produce h5.zf k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P (orderCondition
    oldSide))) h5.hw h5.hs
    h5.hp0 h5.hp1
  let L := ForcingRelationImages.body k (old 5 w) (old 5 f) (old 5 z) (old 5 T) (old 5 S) (old 5 (P 0)) (old 5 (P (orderCondition oldSide)))
  let Ξ := Context.add L (raisedContext 4 Δ)
  apply HornBinderRules.eliminate_many 4 L _ hTables
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have h9 := h5.in_body L
  have hd9 := of_eq (ForcingGuardOpening.direct_rename (old 5 w) (old 5 z) (old 5 f) (old 5 T) (old 5 (P 0)) (old 5 Sg) (old 5 (g 0)) (old 5 (g
    1)) (old 5 Y) (old 4)) (HornBinderRules.under_body 4 hd5 L)
  have hs9 : Derives Ξ (ForcingRelationSource.data R (orderLeaf oldSide) (old 9 w) (old 9 z) (old 9 (g 0)) (old 9 A3) (old 9 f) (old 9 (v
    (ForcingRelationSource.rawSlot (orderLeaf oldSide)))) (old 9 (g 1))
      (old 4 (slot 5 0)) (fun i => old 4 (slot 5 i.succ))) :=
    of_eq (by simp only [E, ForcingRelationSource.body, ForcingRelationSource.data_rename]; rfl) (HornBinderRules.under_body 4 hE L)
  exact order_at_direct test R oldSide (old 9 w) (old 9 z) (old 9 A1) (old 9 A2) (old 9 A3) (old 9 f) (old 9 T) (old 9 C) (old 9 B) (old 9 S) (old
    9 Refl)
    (old 9 Pre) (old 9 j) (old 9 Sg)
    (old 9 (g 0)) (old 9 (g 1)) (old 4 (slot 5 0)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 9 Y)
    (fun i => old 9 (v i)) (fun i => old 9 (Gb i)) (fun i => old 9 (H i))
    (fun i => old 9 (U i)) (fun i => old 9 (F i)) (fun i => old 9 (P i))
    (fun i => old 9 (N i)) (fun i => old 9 (D i)) (fun i => old 4 (slot 5 i.succ))
    h9 hs9 hL hd9

/-- Compare the actual guard with the row’s R(r,p) or R(r,q) leaf. -/
private theorem compare_order_on {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (R : Source.Formula (k+2)) (oldSide : Bool) (w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hA3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 A3)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (P (orderCondition oldSide)) Sg))
    (hg : Derives Γ (ForcingGuardOpening.result true R w z f T (P 0) Sg a head q Y)) :
    Derives Γ (.equal Y (H (ForcingPreorderLeaves.relationPosition (orderLeaf oldSide)))) := by
  have row := Derives.conjL (.conjL (.conjR hd))
  have hParent := Derives.conjL (.conjR (.conjR hd))
  have hs := Derives.conjR (.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hParent))
  have hp0 := Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 0) (F 0) (U 1) (.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR row))))))))))
  have hp1 : Derives Γ (SyntaxTermSyntax.term w z T (P (orderCondition oldSide))) := by
    cases oldSide
    · exact Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 1) (F 1) (U 2) (.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR row))))))))))))
    · exact Derives.conjL (SyntaxTopFormulaTyping.instantiate_environment w z T C (P 2) (F 2) (N 0) (.conjL (.conjR (.conjR (.conjR (.conjR
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR row))))))))))))))
  have h : OrderInputs Γ test R oldSide w z A1 A2 A3 f T C B S Refl Pre j Sg v Gb H U F P N D :=
    ⟨hZ,hw,hz,hA1,hA2,hA3,hf,hj,hd,hr,hs,hp0,hp1⟩
  let E := ForcingGuardOpening.body true R w z f T (P 0) Sg a head q Y
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hg
  have he : Derives Δ E := .hyp (Or.inl rfl)
  exact eq_symm (order_at_guard_data test R oldSide (old 4 w) (old 4 z) (old 4 A1) (old 4 A2) (old 4 A3)
    (old 4 f) (old 4 T) (old 4 C) (old 4 B) (old 4 S) (old 4 Refl) (old 4 Pre) (old 4 j)
    (old 4 Sg) (old 4 a) (old 4 head) (old 4 q) (old 4 Y)
    (fun i => old 4 (v i)) (fun i => old 4 (Gb i)) (fun i => old 4 (H i))
    (fun i => old 4 (U i)) (fun i => old 4 (F i)) (fun i => old 4 (P i))
    (fun i => old 4 (N i)) (fun i => old 4 (D i)) (slot 4) (h.in_body E) he)

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
    Derives Γ (.equal Y (H 3)) :=
  compare_order_on hZ test R false w z A1 A2 A3 f T C B S Refl Pre j Sg a head q Y
    v Gb H U F P N D hw hz hA1 hA2 hA3 hf hj hd hr hg

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
    (test : Formula 1) (Reln : Source.Formula (k+2)) (condition : Fin 3)
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
    (hr : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j (P condition) (v 9))) :
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
  have hr1 := of_eq (ForcingReflexiveImages.replacement_rename w f z B Base j (P condition) (v 9) Fin.castSucc)
    (under hr E)
  have member := ForcingPreorderMember.raw_from_data hZ1 test Reln 0
    w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc B.castSucc C.castSucc T.castSucc Base.castSucc Refl.castSucc Pre.castSucc
      i.castSucc (Fin.last m)
    (fun i => (raw i).castSucc) (fun i => (Gb i).castSucc) (fun i => (H i).castSucc)
    (fun i => (U i).castSucc) (fun i => (F i).castSucc) (fun i => (P i).castSucc) (fun i => (N i).castSucc) (fun i => (D i).castSucc)
    hw1 hz1 h11 h21 hi1 hd1 (.conjR hE)
  exact compare_member hZ1 Reln w.castSucc z.castSucc a.castSucc f.castSucc alpha.castSucc b.castSucc A.castSucc B.castSucc (P 0).castSucc
    R.castSucc S.castSucc n.castSucc x.castSucc Parent.castSucc
    own.castSucc head.castSucc sm.castSucc Y.castSucc Base.castSucc j.castSucc (P condition).castSucc i.castSucc
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
  have member := compare_member_from_row hZ test Reln 1 w z a f alpha b A B R S n x Parent
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
  have member := compare_member_from_row hZ test Reln 1 w z a f alpha b A B R S n x Parent
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


/-- Shared runtime records for the old p-side of the two modal cases. The
raw guard results and tail come from the same old compiled parent. -/
def oldTailInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R S n x Parent v u).conj
    ((SyntaxMixedImageHead.head w alpha f own head).conj
      ((ForcingGuardCode.compiled false Reln w alpha f head sm).conj
        ((guardData Reln w (u 7) (v 9) alpha f z B (P 0) head sm so st si (u 8) r).conj
          ((SyntaxWeakenFreeSyntax.weakened w z b B G (ctx 3)).conj
            ((InternalProofBackground.implication test w z b G Parent).conj
              ((FormulaCodeSyntax.formulaCode w Extra z B).conj
                ((ForcingProofContext.layoutData w z B Extra Pre H ctx).conj
                  ((SyntaxNumeralSyntax.numeral 0 z).conj
                    ((SyntaxNumeralSyntax.numeral 1 A1).conj
                      ((SyntaxNumeralSyntax.numeral 2 A2).conj
                        ((SyntaxNumeralSyntax.numeral 3 A3).conj
                          ((SyntaxNumeralSyntax.numeral (k+2) f).conj
                            ((SyntaxNumeralSyntax.numeral (k+1) j).conj
                              ((SyntaxNumeralSyntax.numeral k i).conj
                                ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B C Bound Base Refl Pre raw Gb H U F P N0 D).conj
                                  ((ForcingReflexiveImages.replacement w f z B Base j (P 2) (v 9))))))))))))))))))

theorem oldTailInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m) (rho : Fin m → Fin l) :
    (oldTailInput test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si v u raw Gb H U F P
      N0 D ctx r).rename rho =
      oldTailInput test Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho R) (rho S) (rho n) (rho x) (rho Parent) (rho
        G) (rho Extra) (rho A1) (rho A2) (rho A3) (rho C) (rho Bound) (rho Base) (rho Refl) (rho Pre) (rho i) (rho j) (rho own) (rho head) (rho
        sm) (rho so) (rho st) (rho si)
        (fun i => rho (v i)) (fun i => rho (u i)) (fun i => rho (raw i)) (fun i => rho (Gb i)) (fun i => rho (H i)) (fun i => rho (U i)) (fun i =>
          rho (F i)) (fun i => rho (P i)) (fun i => rho (N0 i)) (fun i => rho (D i)) (fun i => rho (ctx i)) (fun i => rho (r i)) := by
  simp only [oldTailInput, Formula.rename, ForcingFreshParentOpening.data_rename,
    SyntaxMixedImageHead.head_rename, ForcingGuardCode.compiled_rename, guardData_rename,
    SyntaxWeakenFreeSyntax.weakened_rename, InternalProofBackground.implication_rename,
    FormulaCodeSyntax.formulaCode_rename, ForcingProofContext.layoutData_rename,
    SyntaxNumeralSyntax.numeral_rename, ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename]

/-- Derive the canonical tail proof from the original old parent proof. Both
old guard matches and their proof discharge are internal to this endpoint. -/
private theorem old_tail_from_opened {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m)
    (hi : Derives Γ (oldTailInput test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si v u
      raw Gb H U F P N0 D ctx r)) :
    Derives Γ (ForcingProofContext.resultData test w z B Extra Pre (r 3) H ctx) := by
  have parent := Derives.conjL hi
  have rest := Derives.conjR hi
  have headAt := Derives.conjL rest
  have rest := Derives.conjR rest
  have memberCompiler := Derives.conjL rest
  have rest := Derives.conjR rest
  have rawData := Derives.conjL rest
  have rest := Derives.conjR rest
  have weak := Derives.conjL rest
  have rest := Derives.conjR rest
  have oldProof := Derives.conjL rest
  have rest := Derives.conjR rest
  have extraType := Derives.conjL rest
  have rest := Derives.conjR rest
  have layout := Derives.conjL rest
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
  have oldTable := Derives.conjR rest
  have rawOutputs := Derives.conjL rawData
  have src := Derives.conjL parent
  have hw := Derives.conjL src
  have hz := Derives.conjL (.conjR src)
  have member := compare_member_from_row hZ test Reln 2 w z a f alpha b A B R S n x Parent
    A1 A2 A3 C Bound Base Refl Pre i j own head sm (r 1) v u raw Gb H U F P N0 D
    parent headAt memberCompiler (.conjL (.conjR (.conjL rawOutputs)))
    zero one two free condition carrier row oldTable
  have order := compare_order_on hZ test Reln true w z A1 A2 A3 f B C Bound Base Refl Pre j
    (v 9) alpha head so (r 2) raw Gb H U F P N0 D hw zero one two three free condition row oldTable
    (.conjR (.conjR rawData))
  have outer := SyntaxRenameLogicalSubst.binary_x 2 w (r 1) (r 0) (u 8) (H 0) member (.conjL (.conjL rawOutputs))
  have inner := SyntaxRenameLogicalSubst.binary_x 2 w (r 2) (r 3) (r 0) (H 5) order (.conjL (.conjR rawOutputs))
  have opened := ForcingOldParentInstance.from_opened hZ test w z a f alpha b A B (P 0) R S n x Parent
    G (ctx 3) v u parent weak oldProof
  have hRaw : Derives Γ (substituted w (u 7) (v 9) alpha f z B x (u 8)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR parent))))))))
  have ht := SyntaxMixedFormulaJudgment.target_type w (u 7) (v 9) alpha f z B x (u 8) hRaw
  exact ForcingOldParentInstance.consume_guards hZ test w z B C Refl Pre Extra (u 8) (r 0) (r 3)
    Gb H ctx U F P N0 hw hz extraType ht (.conjL (.conjL (.conjR row))) layout outer inner opened

/-- The canonical nested proof used by the new parent comes from the
actual old parent proof and its actual tail. -/
theorem old_nested_from_opened {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m)
    (hi : Derives Γ (oldTailInput test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si v u
      raw Gb H U F P N0 D ctx r)) :
    Derives Γ (ForcingNestedGuardProof.produced test w z b A B G (ctx 3) (H 0) (H 3) (r 3)) := by
  have hd := old_tail_from_opened hZ test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si
    v u raw Gb H U F P N0 D ctx r hi
  have src := Derives.conjL (.conjL hi)
  have hw := Derives.conjL src
  have tailQuery := Derives.conjR (.conjR (.conjR (.conjL (.conjL (.conjR (.conjR (.conjR hi)))))))
  have hTail := SyntaxMixedFormulaJudgment.target_type w (u 7) (v 9) alpha f z B st (r 3) tailQuery
  have weak := Derives.conjL (.conjR (.conjR (.conjR (.conjR hi))))
  have hG := SyntaxWeakenFreeOutput.source_type hZ w z b B G (ctx 3) hw weak
  exact ForcingNestedGuardProof.produce hZ test w z b A B G Extra Pre (r 3) H ctx
    (.conjI hw (.conjI (.conjL (.conjR src)) (.conjI (.conjL (.conjR (.conjR (.conjR src)))) weak)))
    hG hTail hd

def oldNestedSentence {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m) : Source.Sentence :=
  ((oldTailInput test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si v u raw Gb H U F P
    N0 D ctx r).imp
    (ForcingNestedGuardProof.produced test w z b A B G (ctx 3) (H 0) (H 3) (r 3))).close

theorem old_nested_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm so st si : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) (r : Fin 4 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (oldNestedSentence test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound Base Refl Pre i j own head sm
        so st si v u raw Gb H U F P N0 D ctx r)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact old_nested_from_opened (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z a f alpha b A B R S n x Parent G Extra A1 A2 A3 C Bound
    Base Refl Pre i j own head sm so st si v u raw Gb H U F P N0 D ctx r
    (.hyp (Or.inl rfl))


private def existentialContextData {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z f alpha beta gamma b B j N ParentOld A1 A2 A3 C Bound Base Refl Pre i G Extra Old New : Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m)
    (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) : Formula m :=
  (successor beta alpha).conj
    ((successor gamma beta).conj
    ((FormulaCodeSyntax.formulaCode w N alpha f).conj
    ((SyntaxWeakenFreeSyntax.weakened w z b B G (ctx 3)).conj
    ((InternalProofBackground.implication test w z b G ParentOld).conj
    ((FormulaCodeSyntax.formulaCode w Extra z B).conj
    ((ForcingProofContext.layoutData w z B Extra Pre H ctx).conj
    ((SyntaxNumeralSyntax.numeral 0 z).conj
    ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj
    ((SyntaxNumeralSyntax.numeral 3 A3).conj
    ((SyntaxNumeralSyntax.numeral (k+2) f).conj
    ((SyntaxNumeralSyntax.numeral (k+1) j).conj
    ((SyntaxNumeralSyntax.numeral k i).conj
    ((ForcingPreorderLeaves.data test Reln w z A1 A2 A3 f B C Bound Base Refl Pre raw Gb H U F P N0 D).conj
    ((ForcingReflexiveImages.replacement w f z B Base j (P 2) Old).conj
    (ForcingReflexiveImages.replacement w f z B Base j (P 1) New))))))))))))))))

private def existentialTransferData {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b B j N n ParentOld A1 A2 A3 C Bound Base Refl Pre i G Extra Old New : Fin m)
    (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m)
    (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) : Formula m :=
  (ForcingExistCode.data Reln Dom w a alpha beta gamma f j N n cv).conj
    ((ForcingExistCode.shellData w a alpha beta gamma f (cv 2) (cv 3) (cv 4) (cv 5) (cv 6) (cv 7) n sv).conj
    (existentialContextData test Reln w z f alpha beta gamma b B j N ParentOld A1 A2 A3 C Bound Base
      Refl Pre i G Extra Old New raw Gb H U F P N0 D ctx))

/-- Both openings use the same existential compiler record. The preorder row
and weakened context are the ones used to derive the old parent's tail. -/
private def pairedExistentialInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra : Fin m)
    (vOld : Fin 10 → Fin m) (uOld : Fin 9 → Fin m)
    (vNew : Fin 10 → Fin m) (uNew : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R SOld n x ParentOld vOld uOld).conj
    ((ForcingFreshParentOpening.data w z a f alpha b A B (P 0) R SNew n x ParentNew vNew uNew).conj
    (existentialTransferData test Reln Dom w z a f alpha beta gamma b B j N n ParentOld A1 A2 A3 C Bound Base Refl Pre i G Extra
      (vOld 9) (vNew 9) cv sv raw Gb H U F P N0 D ctx))

private theorem pairedExistentialInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra : Fin m)
    (vOld : Fin 10 → Fin m) (uOld : Fin 9 → Fin m)
    (vNew : Fin 10 → Fin m) (uNew : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) (rho : Fin m → Fin l) :
    (pairedExistentialInput test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl
      Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx).rename rho =
      pairedExistentialInput test Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta) (rho gamma) (rho b) (rho A)
        (rho B) (rho R) (rho SOld) (rho SNew) (rho j) (rho N) (rho n) (rho x) (rho ParentOld) (rho ParentNew) (rho A1) (rho A2) (rho A3)
        (rho C) (rho Bound) (rho Base) (rho Refl) (rho Pre) (rho i) (rho G) (rho Extra) (fun s => rho (vOld s))
        (fun s => rho (uOld s)) (fun s => rho (vNew s)) (fun s => rho (uNew s)) (fun s => rho (cv s)) (fun s => rho (sv s))
        (fun s => rho (raw s)) (fun s => rho (Gb s)) (fun s => rho (H s)) (fun s => rho (U s)) (fun s => rho (F s))
        (fun s => rho (P s)) (fun s => rho (N0 s)) (fun s => rho (D s)) (fun s => rho (ctx s)) := by
  simp only [pairedExistentialInput, existentialTransferData, existentialContextData, Formula.rename, ForcingFreshParentOpening.data_rename,
    ForcingExistCode.data_rename,
    ForcingExistCode.shellData_rename,
    successor_rename,
    FormulaCodeSyntax.formulaCode_rename,
    SyntaxWeakenFreeSyntax.weakened_rename,
    InternalProofBackground.implication_rename,
    ForcingProofContext.layoutData_rename,
    SyntaxNumeralSyntax.numeral_rename,
    ForcingPreorderLeaves.data_rename,
    ForcingReflexiveImages.replacement_rename]

private theorem shared_prefixed_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f alpha b A B t R SOld SNew n x ParentOld ParentNew : Fin m)
    (vOld vNew : Fin 10 → Fin m) (uOld uNew : Fin 9 → Fin m)
    (sameBound : vNew 8 = vOld 8)
    (hpOld : Derives Γ (ForcingFreshParentOpening.data w z a f alpha b A B t R SOld n x ParentOld vOld uOld))
    (hpNew : Derives Γ (ForcingFreshParentOpening.data w z a f alpha b A B t R SNew n x ParentNew vNew uNew)) :
    Derives Γ (.equal (uOld 7) (uNew 7)) := by
  have hw := Derives.conjL (.conjL hpOld)
  have ht := SyntaxTerms.range hZ w z B t hw
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjL hpOld))))))))
  have lists := SyntaxMixedImageCodePairs.term_lists w (vOld 6) (vOld 7) a f z B (vOld 8) (vOld 9)
    (.conjR (.conjR (.conjR (.conjR (.conjL (.conjR hpOld))))))
  have boundNat : Derives Γ (.mem (vOld 8) w) := .conjL (.conjL (.conjR (.conjR (.conjL lists))))
  have oldCons : Derives Γ (StructuralListSyntax.consCode w t (vOld 8) (uOld 7)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hpOld)))))))
  have newCons : Derives Γ (StructuralListSyntax.consCode w t (vNew 8) (uNew 7)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hpNew)))))))
  exact StructuralConsUnique.unique hZ w t (vOld 8) (uOld 7) (uNew 7) hw ht boundNat
    oldCons (sameBound ▸ newCons)

set_option maxHeartbeats 1000000 in
private theorem existential_at_old_nested {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra : Fin m)
    (vOld : Fin 10 → Fin m) (uOld : Fin 9 → Fin m)
    (vNew : Fin 10 → Fin m) (uNew : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m)
    (r : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (sameBound : vNew 8 = vOld 8)
    (hi : Derives Γ (pairedExistentialInput test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl
      Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx))
    (hr : Derives Γ (guardData Reln w (uOld 7) (vOld 9) alpha f z B (P 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (uOld 8) r))
    (hn : Derives Γ (ForcingNestedGuardProof.data test w z b A B G (ctx 3) (H 0) (H 3) (r 3) (s 0) (s 1) (s 2))) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) := by
  have hpOld := Derives.conjL hi
  have rest := Derives.conjR hi
  have hpNew := Derives.conjL rest
  have rest := Derives.conjR rest
  have compiler := Derives.conjL rest
  have rest := Derives.conjR rest
  have shellFields := Derives.conjL rest
  have rest := Derives.conjR rest
  have hBeta := Derives.conjL rest
  have rest := Derives.conjR rest
  have hGamma := Derives.conjL rest
  have rest := Derives.conjR rest
  have child := Derives.conjL rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
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
  have newTable := rest
  have boundEq := shared_prefixed_bound hZ w z a f alpha b A B (P 0) R SOld SNew n x ParentOld ParentNew
    vOld vNew uOld uNew sameBound hpOld hpNew
  have tail := SyntaxMixedFormulaJudgmentSubst.subst_r w (uOld 7) (vOld 9) alpha f z B (sv 4) (r 3)
    (uNew 7) boundEq (.conjR (.conjR (.conjR (.conjL hr))))
  apply consume_existential_root hZ test Reln Dom w z a f alpha beta gamma b A B R SNew j N n x ParentNew
    A1 A2 A3 C Bound Base Refl Pre i (vOld 9) (r 3) G (ctx 3) (s 0) (s 1) (s 2)
    vNew uNew cv sv raw Gb H U F P N0 D
  exact .conjI hpNew (.conjI compiler (.conjI shellFields (.conjI hBeta (.conjI hGamma (.conjI child
    (.conjI zero (.conjI one (.conjI two (.conjI three (.conjI free (.conjI condition (.conjI carrier
      (.conjI row (.conjI oldTable (.conjI newTable (.conjI tail hn))))))))))))))))

set_option maxHeartbeats 1000000 in
private theorem existential_at_old_guards {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra : Fin m)
    (vOld : Fin 10 → Fin m) (uOld : Fin 9 → Fin m)
    (vNew : Fin 10 → Fin m) (uNew : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m)
    (r : Fin 4 → Fin m)
    (sameBound : vNew 8 = vOld 8)
    (hi : Derives Γ (pairedExistentialInput test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl
      Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx))
    (hr : Derives Γ (guardData Reln w (uOld 7) (vOld 9) alpha f z B (P 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5) (uOld 8) r)) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) := by
  have hpOld := Derives.conjL hi
  have rest := Derives.conjR hi
  have rest := Derives.conjR rest
  have compiler := Derives.conjL rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have rest := Derives.conjR rest
  have weak := Derives.conjL rest
  have rest := Derives.conjR rest
  have oldProof := Derives.conjL rest
  have rest := Derives.conjR rest
  have extraType := Derives.conjL rest
  have rest := Derives.conjR rest
  have layout := Derives.conjL rest
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
  have head := head_at_parent hZ w z a f alpha b A B (P 0) R SOld n x ParentOld gamma
    (cv 0) (cv 1) (.conjL hpOld) (.conjL compiler)
  have nested := old_nested_from_opened hZ test Reln w z a f alpha b A B R SOld n x ParentOld G Extra
    A1 A2 A3 C Bound Base Refl Pre i j (cv 0) (cv 1) (cv 2) (cv 3) (sv 4) (sv 5)
    vOld uOld raw Gb H U F P N0 D ctx r
    (.conjI hpOld (.conjI head (.conjI (.conjL (.conjR compiler)) (.conjI hr (.conjI weak (.conjI oldProof
      (.conjI extraType (.conjI layout (.conjI zero (.conjI one (.conjI two (.conjI three (.conjI free
        (.conjI condition (.conjI carrier (.conjI row oldTable))))))))))))))))
  let E := ForcingNestedGuardProof.body test w z b A B G (ctx 3) (H 0) (H 3) (r 3)
  apply HornBinderRules.eliminate_many 3 E _ nested
  have hi3 := of_eq (pairedExistentialInput_rename test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound
      Base Refl Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx (old 3))
    (HornBinderRules.under_body 3 hi E)
  have hr3 := of_eq (guardData_rename Reln w (uOld 7) (vOld 9) alpha f z B (P 0) (cv 1) (cv 2) (cv 3)
      (sv 4) (sv 5) (uOld 8) r (old 3)) (HornBinderRules.under_body 3 hr E)
  apply of_eq (InternalProofBackground.implication_rename test w z b G ParentNew (old 3)).symm
  exact existential_at_old_nested (HornBinderRules.zf_body 3 hZ E) test Reln Dom (old 3 w) (old 3 z) (old 3 a) (old 3 f)
    (old 3 alpha) (old 3 beta) (old 3 gamma) (old 3 b) (old 3 A) (old 3 B) (old 3 R) (old 3 SOld) (old 3 SNew) (old 3 j) (old 3 N) (old 3 n)
    (old 3 x) (old 3 ParentOld) (old 3 ParentNew) (old 3 A1) (old 3 A2) (old 3 A3) (old 3 C) (old 3 Bound) (old 3 Base)
    (old 3 Refl) (old 3 Pre) (old 3 i) (old 3 G) (old 3 Extra) (fun s => old 3 (vOld s)) (fun s => old 3 (uOld s))
    (fun s => old 3 (vNew s)) (fun s => old 3 (uNew s)) (fun s => old 3 (cv s)) (fun s => old 3 (sv s))
    (fun s => old 3 (raw s)) (fun s => old 3 (Gb s)) (fun s => old 3 (H s)) (fun s => old 3 (U s)) (fun s => old 3 (F s))
    (fun s => old 3 (P s)) (fun s => old 3 (N0 s)) (fun s => old 3 (D s)) (fun s => old 3 (ctx s)) (fun s => old 3 (r s))
    (slot 3) (congrArg (old 3) sameBound) hi3 hr3 (.hyp (Or.inl rfl))

set_option maxHeartbeats 1000000 in
/-- Produce the nested proof from the old actual parent and consume it on
the new actual parent with the same existential compilation record. -/
private theorem transfer_existential_opened {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra : Fin m)
    (vOld : Fin 10 → Fin m) (uOld : Fin 9 → Fin m)
    (vNew : Fin 10 → Fin m) (uNew : Fin 9 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m)
    (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m)
    (sameBound : vNew 8 = vOld 8)
    (hi : Derives Γ (pairedExistentialInput test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl
      Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx)) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) := by
  have hpOld := Derives.conjL hi
  have rest := Derives.conjR hi
  have rest := Derives.conjR rest
  have compiler := Derives.conjL rest
  have rest := Derives.conjR rest
  have shellFields := Derives.conjL rest
  have record := existential_at_records hZ Reln Dom w z a f alpha beta gamma b A B (P 0) R SOld j N n x ParentOld
    vOld uOld cv sv hpOld compiler shellFields
  let E := guardData Reln (old 4 w) (old 4 (uOld 7)) (old 4 (vOld 9)) (old 4 alpha) (old 4 f) (old 4 z)
    (old 4 B) (old 4 (P 0)) (old 4 (cv 1)) (old 4 (cv 2)) (old 4 (cv 3)) (old 4 (sv 4)) (old 4 (sv 5))
    (old 4 (uOld 8)) (slot 4)
  apply HornBinderRules.eliminate_many 4 E _ (.conjR (.conjR (.conjR record)))
  have hi4 := of_eq (pairedExistentialInput_rename test Reln Dom w z a f alpha beta gamma b A B R SOld SNew j N n x ParentOld ParentNew A1 A2 A3 C Bound
      Base Refl Pre i G Extra vOld uOld vNew uNew cv sv raw Gb H U F P N0 D ctx (old 4))
    (HornBinderRules.under_body 4 hi E)
  apply of_eq (InternalProofBackground.implication_rename test w z b G ParentNew (old 4)).symm
  exact existential_at_old_guards (HornBinderRules.zf_body 4 hZ E) test Reln Dom (old 4 w) (old 4 z) (old 4 a) (old 4 f)
    (old 4 alpha) (old 4 beta) (old 4 gamma) (old 4 b) (old 4 A) (old 4 B) (old 4 R) (old 4 SOld) (old 4 SNew) (old 4 j) (old 4 N) (old 4 n)
    (old 4 x) (old 4 ParentOld) (old 4 ParentNew) (old 4 A1) (old 4 A2) (old 4 A3) (old 4 C) (old 4 Bound) (old 4 Base)
    (old 4 Refl) (old 4 Pre) (old 4 i) (old 4 G) (old 4 Extra) (fun s => old 4 (vOld s)) (fun s => old 4 (uOld s))
    (fun s => old 4 (vNew s)) (fun s => old 4 (uNew s)) (fun s => old 4 (cv s)) (fun s => old 4 (sv s))
    (fun s => old 4 (raw s)) (fun s => old 4 (Gb s)) (fun s => old 4 (H s)) (fun s => old 4 (U s)) (fun s => old 4 (F s))
    (fun s => old 4 (P s)) (fun s => old 4 (N0 s)) (fun s => old 4 (D s)) (fun s => old 4 (ctx s)) (slot 4)
    (congrArg (old 4) sameBound) hi4 (.hyp (Or.inl rfl))



/-- Both source parents are opened on the same weakened base table, with
their own original and weakened condition replacements. -/
def existentialFramesInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m)
    (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) : Formula m :=
  (ForcingRawGuardOpening.overwrittenInput w z a f alpha b A B (P 0) R S j QOld (P 2) SOld Old n x ParentOld v).conj
    ((ForcingRawGuardOpening.overwrittenInput w z a f alpha b A B (P 0) R S j QNew (P 1) SNew New n x ParentNew v).conj
      (existentialTransferData test Reln Dom w z a f alpha beta gamma b B j N n ParentOld A1 A2 A3 C Bound Base Refl Pre i G
      Extra Old New cv sv raw Gb H U F P N0 D ctx))

set_option maxHeartbeats 1500000 in
private theorem with_overwrites {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f alpha b A B t R S j n x ParentOld ParentNew QOld QNew TOld TNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (target : Formula m)
    (hoInput : Derives Γ (ForcingRawGuardOpening.overwrittenInput w z a f alpha b A B t R S j QOld TOld SOld Old n x ParentOld v))
    (hnInput : Derives Γ (ForcingRawGuardOpening.overwrittenInput w z a f alpha b A B t R S j QNew TNew SNew New n x ParentNew v))
    (consume : ∀ {l} {Δ : Context l} (rho : Fin m → Fin l) (vo vn : Fin 10 → Fin l) (uo un : Fin 9 → Fin l),
      ZFContext.Evidence Δ → (∀ {p}, Derives Γ p → Derives Δ (p.rename rho)) →
      vn 8 = vo 8 → vo 9 = rho Old → vn 9 = rho New →
      Derives Δ (ForcingFreshParentOpening.data (rho w) (rho z) (rho a) (rho f) (rho alpha)
        (rho b) (rho A) (rho B) (rho t) (rho R) (rho SOld) (rho n) (rho x) (rho ParentOld) vo uo) →
      Derives Δ (ForcingFreshParentOpening.data (rho w) (rho z) (rho a) (rho f) (rho alpha)
        (rho b) (rho A) (rho B) (rho t) (rho R) (rho SNew) (rho n) (rho x) (rho ParentNew) vn un) →
      Derives Δ (target.rename rho)) : Derives Γ target := by
  have ho := ForcingRawGuardOpening.open_overwritten hZ w z a f alpha b A B t R S j QOld TOld SOld Old n x ParentOld v
      hoInput
  have hn := ForcingRawGuardOpening.open_overwritten hZ w z a f alpha b A B t R S j QNew TNew SNew New n x ParentNew v
      hnInput
  let EOld := ForcingRawGuardOpening.overwrittenBody w z a f alpha b A B t R SOld Old n x ParentOld v
  let BOld := ForcingRawGuardOpening.overwrittenData w z a f alpha b A B t R SOld Old n x ParentOld v
  let ΓOld := Context.add BOld (raisedContext 9 (Context.add EOld (raisedContext 2 Γ)))
  let first := fun i : Fin m => old 9 (old 2 i)
  apply ForcingRawGuardOpening.eliminate_overwritten w z a f alpha b A B t R SOld Old n x ParentOld v target ho
  have moveOld {p : Formula m} (h : Derives Γ p) : Derives ΓOld (p.rename first) :=
    of_eq (rename_comp p (old 2) (old 9))
      (HornBinderRules.under_body 9 (HornBinderRules.under_body 2 h EOld) BOld)
  have hpOld : Derives ΓOld BOld := .hyp (Or.inl rfl)
  have hnOld : Derives ΓOld (ForcingRawGuardOpening.overwritten (first w) (first z) (first a) (first f) (first alpha)
      (first b) (first A) (first B) (first t) (first R) (first SNew) (first New) (first n) (first x) (first ParentNew)
      (fun s => first (v s))) := by
    simpa only [ForcingRawGuardOpening.overwritten_rename] using moveOld hn
  let ENew := ForcingRawGuardOpening.overwrittenBody (first w) (first z) (first a) (first f) (first alpha) (first b)
      (first A) (first B) (first t) (first R) (first SNew) (first New) (first n) (first x) (first ParentNew)
      (fun s => first (v s))
  let BNew := ForcingRawGuardOpening.overwrittenData (first w) (first z) (first a) (first f) (first alpha) (first b)
      (first A) (first B) (first t) (first R) (first SNew) (first New) (first n) (first x) (first ParentNew)
      (fun s => first (v s))
  let ΓNew := Context.add BNew (raisedContext 9 (Context.add ENew (raisedContext 2 ΓOld)))
  let second := fun i : Fin ((m+2)+9) => old 9 (old 2 i)
  let both := fun i => second (first i)
  apply ForcingRawGuardOpening.eliminate_overwritten (first w) (first z) (first a) (first f) (first alpha) (first b)
      (first A) (first B) (first t) (first R) (first SNew) (first New) (first n) (first x) (first ParentNew)
      (fun s => first (v s)) _ hnOld
  have moveNew {p : Formula ((m+2)+9)} (h : Derives ΓOld p) : Derives ΓNew (p.rename second) :=
    of_eq (rename_comp p (old 2) (old 9))
      (HornBinderRules.under_body 9 (HornBinderRules.under_body 2 h ENew) BNew)
  have hpNew : Derives ΓNew BNew := .hyp (Or.inl rfl)
  let firstImages := fun i => old 9 (ForcingRawGuardOpening.overwriteImages
    (fun s => old 2 (v s)) (slot 2 0) (slot 2 1) (old 2 Old) i)
  let vOld := fun i => second (firstImages i)
  let vNew := fun i => old 9 (ForcingRawGuardOpening.overwriteImages
    (fun s => old 2 (first (v s))) (slot 2 0) (slot 2 1) (old 2 (first New)) i)
  have oldMoved := of_eq (ForcingFreshParentOpening.data_rename (first w) (first z) (first a) (first f)
    (first alpha) (first b) (first A) (first B) (first t) (first R) (first SOld) (first n)
    (first x) (first ParentOld) firstImages (slot 9) second) (moveNew hpOld)
  have zfOld := HornBinderRules.zf_body 9 (HornBinderRules.zf_body 2 hZ EOld) BOld
  have zfNew := HornBinderRules.zf_body 9 (HornBinderRules.zf_body 2 zfOld ENew) BNew
  have result := consume both vOld vNew (fun i => second (slot 9 i)) (slot 9) zfNew
    (fun h => of_eq (rename_comp _ first second) (moveNew (moveOld h)))
    rfl rfl rfl oldMoved hpNew
  simpa only [rename_comp, both] using result

set_option maxHeartbeats 1500000 in
/-- Produce both original openings, transfer their actual tail proof, and
return the original new-parent implication. -/
theorem transfer_existential_from_frames {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m)
    (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m)
    (hi : Derives Γ (existentialFramesInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base
      Refl Pre i G Extra QOld QNew SOld SNew Old New v cv sv raw Gb H U F P N0 D ctx)) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) := by
  have shared := Derives.conjR (.conjR hi)
  apply with_overwrites hZ w z a f alpha b A B (P 0) R S j n x ParentOld ParentNew QOld QNew (P 2) (P 1)
    SOld SNew Old New v _ (.conjL hi) (.conjL (.conjR hi))
  intro l Δ both vOld vNew uOld uNew zf move sameBound oldFree newFree hpOld hpNew
  have hshared : Derives Δ (existentialTransferData test Reln Dom (both w) (both z) (both a) (both f) (both alpha)
      (both beta) (both gamma) (both b) (both B) (both j) (both N) (both n) (both ParentOld) (both A1) (both A2) (both A3)
      (both C) (both Bound) (both Base) (both Refl) (both Pre) (both i) (both G) (both Extra) (both Old) (both New)
      (fun s => both (cv s)) (fun s => both (sv s)) (fun s => both (raw s)) (fun s => both (Gb s)) (fun s => both (H s))
      (fun s => both (U s)) (fun s => both (F s)) (fun s => both (P s)) (fun s => both (N0 s)) (fun s => both (D s))
      (fun s => both (ctx s))) := by
    simpa only [existentialTransferData, existentialContextData, Formula.rename,
      ForcingExistCode.data_rename, ForcingExistCode.shellData_rename, successor_rename,
      FormulaCodeSyntax.formulaCode_rename, SyntaxWeakenFreeSyntax.weakened_rename,
      InternalProofBackground.implication_rename, ForcingProofContext.layoutData_rename,
      SyntaxNumeralSyntax.numeral_rename, ForcingPreorderLeaves.data_rename,
      ForcingReflexiveImages.replacement_rename] using move shared
  have result := transfer_existential_opened zf test Reln Dom (both w) (both z) (both a) (both f) (both alpha) (both beta)
      (both gamma) (both b) (both A) (both B) (both R) (both SOld) (both SNew) (both j) (both N) (both n) (both x)
      (both ParentOld) (both ParentNew) (both A1) (both A2) (both A3) (both C) (both Bound) (both Base) (both Refl)
      (both Pre) (both i) (both G) (both Extra) vOld uOld vNew uNew (fun s => both (cv s))
      (fun s => both (sv s)) (fun s => both (raw s)) (fun s => both (Gb s)) (fun s => both (H s)) (fun s => both (U s))
      (fun s => both (F s)) (fun s => both (P s)) (fun s => both (N0 s)) (fun s => both (D s)) (fun s => both (ctx s)) sameBound
    (.conjI hpOld (.conjI hpNew (by simpa only [oldFree, newFree] using hshared)))
  simpa only [InternalProofBackground.implication_rename] using result

theorem transfer_existential_from_frames_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (cv : Fin 8 → Fin m) (sv : Fin 7 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m)
    (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (ctx : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence
        ((existentialFramesInput test Reln Dom w z a f alpha beta gamma b A B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base
            Refl Pre i G Extra QOld QNew SOld SNew Old New v cv sv raw Gb H U F P N0 D ctx).imp
          (InternalProofBackground.implication test w z b G ParentNew)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact transfer_existential_from_frames (ZFContext.add (ZFContext.source_ZF m) _) test Reln Dom w z a f alpha beta gamma b A
      B R S j N n x ParentOld ParentNew A1 A2 A3 C Bound Base Refl Pre i G Extra QOld QNew SOld SNew Old New v cv sv raw Gb H
      U F P N0 D ctx (.hyp (Or.inl rfl))


private structure NegativeArgs (m : Nat) where
  w : Fin m
  z : Fin m
  a : Fin m
  f : Fin m
  alpha : Fin m
  b : Fin m
  A : Fin m
  B : Fin m
  R : Fin m
  S : Fin m
  j : Fin m
  N : Fin m
  n : Fin m
  ParentOld : Fin m
  ParentNew : Fin m
  A1 : Fin m
  A2 : Fin m
  A3 : Fin m
  C : Fin m
  Bound : Fin m
  Refl : Fin m
  Pre : Fin m
  i : Fin m
  G : Fin m
  Extra : Fin m
  QOld : Fin m
  QNew : Fin m
  SOld : Fin m
  SNew : Fin m
  Old : Fin m
  New : Fin m
  v : Fin 10 → Fin m
  raw : Fin 16 → Fin m
  Gb : Fin 5 → Fin m
  H : Fin 6 → Fin m
  U : Fin 3 → Fin m
  F : Fin 3 → Fin m
  P : Fin 3 → Fin m
  N0 : Fin 5 → Fin m
  D : Fin 3 → Fin m
  ctx : Fin 6 → Fin m

private def NegativeArgs.map {m l} (p : NegativeArgs m) (rho : Fin m → Fin l) : NegativeArgs l :=
  ⟨rho p.w, rho p.z, rho p.a, rho p.f, rho p.alpha, rho p.b, rho p.A, rho p.B, rho p.R, rho p.S, rho p.j, rho p.N, rho p.n,
    rho p.ParentOld, rho p.ParentNew, rho p.A1, rho p.A2, rho p.A3, rho p.C, rho p.Bound, rho p.Refl, rho p.Pre, rho p.i, rho p.G,
    rho p.Extra, rho p.QOld, rho p.QNew, rho p.SOld, rho p.SNew, rho p.Old, rho p.New, (fun i => rho (p.v i)),
    (fun i => rho (p.raw i)), (fun i => rho (p.Gb i)), (fun i => rho (p.H i)), (fun i => rho (p.U i)), (fun i => rho (p.F i)),
    (fun i => rho (p.P i)), (fun i => rho (p.N0 i)), (fun i => rho (p.D i)), (fun i => rho (p.ctx i))⟩

private def NegativeArgs.goal {m} (test : Formula 1) (p : NegativeArgs m) : Formula m :=
  InternalProofBackground.implication test p.w p.z p.b p.G p.ParentNew

private structure NegativeOpened {k m} (Γ : Context m) (test : Formula 1) (Reln : Source.Formula (k+2))
    (p : NegativeArgs m) (cv : Fin 5 → Fin m) (sv : Fin 4 → Fin m)
    (vo vn : Fin 10 → Fin m) (uo un : Fin 9 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  parentOld : Derives Γ (ForcingFreshParentOpening.data p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SOld p.n (sv 3)
      p.ParentOld vo uo)
  parentNew : Derives Γ (ForcingFreshParentOpening.data p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SNew p.n (sv 3)
      p.ParentNew vn un)
  compiler : Derives Γ (ForcingNegCode.data Reln p.w p.a p.alpha p.f p.j p.N p.n cv)
  shell : Derives Γ (ForcingNegCode.shellData p.w p.a p.alpha p.f (cv 3) (cv 4) (cv 2) p.n sv)
  full : Derives Γ (ForcingNegCode.compiled Reln p.w p.a p.alpha p.f p.j p.N p.n)
  childType : Derives Γ (FormulaCodeSyntax.formulaCode p.w p.N p.a p.f)
  weak : Derives Γ (SyntaxWeakenFreeSyntax.weakened p.w p.z p.b p.B p.G (p.ctx 3))
  oldProof : Derives Γ (InternalProofBackground.implication test p.w p.z p.b p.G p.ParentOld)
  extraType : Derives Γ (FormulaCodeSyntax.formulaCode p.w p.Extra p.z p.B)
  layout : Derives Γ (ForcingProofContext.layoutData p.w p.z p.B p.Extra p.Pre p.H p.ctx)
  zero : Derives Γ (SyntaxNumeralSyntax.numeral 0 p.z)
  one : Derives Γ (SyntaxNumeralSyntax.numeral 1 p.A1)
  two : Derives Γ (SyntaxNumeralSyntax.numeral 2 p.A2)
  three : Derives Γ (SyntaxNumeralSyntax.numeral 3 p.A3)
  free : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) p.f)
  carrier : Derives Γ (SyntaxNumeralSyntax.numeral k p.i)
  row : Derives Γ (ForcingPreorderLeaves.data test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.B p.C p.Bound (p.v 9) p.Refl p.Pre p.raw
      p.Gb p.H p.U p.F p.P p.N0 p.D)
  oldTable : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 2) (vo 9))
  newTable : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 1) (vn 9))
  baseType : Derives Γ (SyntaxMixedImageCodeSyntax.termList p.w p.f p.z p.B (p.v 9))

private theorem NegativeOpened.in_body {k m l} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (E : Formula (m+l)) :
    NegativeOpened (Context.add E (raisedContext l Γ)) test Reln (p.map (old l))
      (fun i => old l (cv i)) (fun i => old l (sv i))
      (fun i => old l (vo i)) (fun i => old l (vn i)) (fun i => old l (uo i)) (fun i => old l (un i)) := by
  constructor
  · exact HornBinderRules.zf_body l h.zf E
  · simpa only [NegativeArgs.map, ForcingFreshParentOpening.data_rename] using HornBinderRules.under_body l h.parentOld E
  · simpa only [NegativeArgs.map, ForcingFreshParentOpening.data_rename] using HornBinderRules.under_body l h.parentNew E
  · simpa only [NegativeArgs.map, ForcingNegCode.data_rename] using HornBinderRules.under_body l h.compiler E
  · simpa only [NegativeArgs.map, ForcingNegCode.shellData_rename] using HornBinderRules.under_body l h.shell E
  · simpa only [NegativeArgs.map, ForcingNegCode.compiled_rename] using HornBinderRules.under_body l h.full E
  · simpa only [NegativeArgs.map, FormulaCodeSyntax.formulaCode_rename] using HornBinderRules.under_body l h.childType E
  · simpa only [NegativeArgs.map, SyntaxWeakenFreeSyntax.weakened_rename] using HornBinderRules.under_body l h.weak E
  · simpa only [NegativeArgs.map, InternalProofBackground.implication_rename] using HornBinderRules.under_body l h.oldProof E
  · simpa only [NegativeArgs.map, FormulaCodeSyntax.formulaCode_rename] using HornBinderRules.under_body l h.extraType E
  · simpa only [NegativeArgs.map, ForcingProofContext.layoutData_rename] using HornBinderRules.under_body l h.layout E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.zero E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.one E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.two E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.three E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.free E
  · simpa only [NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using HornBinderRules.under_body l h.carrier E
  · simpa only [NegativeArgs.map, ForcingPreorderLeaves.data_rename] using HornBinderRules.under_body l h.row E
  · simpa only [NegativeArgs.map, ForcingReflexiveImages.replacement_rename] using HornBinderRules.under_body l h.oldTable E
  · simpa only [NegativeArgs.map, ForcingReflexiveImages.replacement_rename] using HornBinderRules.under_body l h.newTable E
  · simpa only [NegativeArgs.map, SyntaxMixedImageCodeSyntax.termList_rename] using HornBinderRules.under_body l h.baseType E


private theorem NegativeArgs.goal_rename {m l} (test : Formula 1) (p : NegativeArgs m) (rho : Fin m → Fin l) :
    (p.goal test).rename rho = (p.map rho).goal test :=
  InternalProofBackground.implication_rename test p.w p.z p.b p.G p.ParentNew rho

set_option maxHeartbeats 1000000 in
private theorem negative_at_nested {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (sameBound : vn 8 = vo 8)
    (Sel Operand : Fin m)
    (hSel : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 0) Sel))
    (hOperand : Derives Γ (substituted p.w (vo 8) Sel p.a p.f p.z p.B p.N Operand))
    (r : Fin 4 → Fin m)
    (hr : Derives Γ (guardData Reln p.w (uo 7) (vo 9) p.alpha p.f p.z p.B (p.P 0)
      (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (uo 8) r))
    (s : Fin 3 → Fin m)
    (hs : Derives Γ (ForcingNestedGuardProof.data test p.w p.z p.b p.A p.B p.G (p.ctx 3)
      (p.H 0) (p.H 3) (r 3) (s 0) (s 1) (s 2))) : Derives Γ (p.goal test) := by
  have src := Derives.conjL h.parentOld
  have hw := Derives.conjL src
  have hz := Derives.conjL (.conjR src)
  have hTerm := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))
  have hCons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.parentOld)))))))
  have bot : Derives Γ (SyntaxNodeSyntax.constructor 0 0 p.w Fin.elim0 (sv 0)) := .conjL (.conjL h.shell)
  have tail := ForcingRawNegTail.canonical_code h.zf p.w p.z p.a p.alpha p.f p.B (vo 8) (uo 7) (vo 9) (p.v 9)
    p.j (p.P 0) (p.P 2) Sel p.N (cv 2) (sv 0) (sv 1) (r 3) Operand (sv 0)
    hw hz hTerm hCons h.oldTable hSel (.conjL (.conjR h.compiler)) (.conjL (.conjL (.conjR h.shell)))
    bot (.conjR (.conjR (.conjR (.conjL hr)))) hOperand bot
  have operandNew : Derives Γ (substituted p.w (vn 8) Sel p.a p.f p.z p.B p.N Operand) := by
    simpa only [sameBound] using hOperand
  have records := negative_at_records h.zf Reln p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SNew p.j
    p.N p.n (sv 3) p.ParentNew vn un cv sv h.parentNew h.compiler h.shell
  apply negative_root_at_records h.zf test Reln p.w p.z p.a p.f p.alpha p.b p.A p.B p.R p.SNew p.j p.N p.n
    (sv 3) p.ParentNew p.A1 p.A2 p.A3 p.C p.Bound (p.v 9) p.Refl p.Pre p.i Sel Operand (sv 0) (r 3)
    p.G (p.ctx 3) (s 0) (s 1) (s 2) vn un p.raw p.Gb p.H p.U p.F p.P p.N0 p.D cv sv _ records
  refine .conjI h.parentNew (.conjI h.full (.conjI h.zero (.conjI h.one (.conjI h.two (.conjI h.three ?_)))))
  exact .conjI h.free (.conjI (.conjL h.full) (.conjI h.carrier (.conjI h.row (.conjI hSel
    (.conjI h.newTable (.conjI operandNew (.conjI bot (.conjI tail hs))))))))

set_option maxHeartbeats 1000000 in
private theorem negative_at_guards {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (sameBound : vn 8 = vo 8)
    (Sel Operand : Fin m)
    (hSel : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 0) Sel))
    (hOperand : Derives Γ (substituted p.w (vo 8) Sel p.a p.f p.z p.B p.N Operand))
    (r : Fin 4 → Fin m)
    (hr : Derives Γ (guardData Reln p.w (uo 7) (vo 9) p.alpha p.f p.z p.B (p.P 0)
      (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) (uo 8) r)) : Derives Γ (p.goal test) := by
  have nested := old_nested_from_opened h.zf test Reln p.w p.z p.a p.f p.alpha p.b p.A p.B p.R p.SOld
    p.n (sv 3) p.ParentOld p.G p.Extra p.A1 p.A2 p.A3 p.C p.Bound (p.v 9) p.Refl p.Pre p.i p.j
    (cv 0) (cv 1) (cv 3) (cv 4) (sv 1) (sv 2) vo uo p.raw p.Gb p.H p.U p.F p.P p.N0 p.D p.ctx r
    (.conjI h.parentOld (.conjI (.conjL h.compiler) (.conjI (.conjL (.conjR (.conjR h.compiler)))
      (.conjI hr (.conjI h.weak (.conjI h.oldProof (.conjI h.extraType (.conjI h.layout (.conjI h.zero
        (.conjI h.one (.conjI h.two (.conjI h.three (.conjI h.free (.conjI (.conjL h.full)
          (.conjI h.carrier (.conjI h.row h.oldTable))))))))))))))))
  let E := ForcingNestedGuardProof.body test p.w p.z p.b p.A p.B p.G (p.ctx 3) (p.H 0) (p.H 3) (r 3)
  apply HornBinderRules.eliminate_many 3 E _ nested
  apply of_eq (NegativeArgs.goal_rename test p (old 3)).symm
  exact negative_at_nested (h.in_body E) (congrArg (old 3) sameBound) (old 3 Sel) (old 3 Operand)
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (old 3)) (HornBinderRules.under_body 3 hSel E))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (old 3)) (HornBinderRules.under_body 3 hOperand E))
    (fun i => old 3 (r i))
    (of_eq (guardData_rename Reln _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (old 3)) (HornBinderRules.under_body 3 hr E))
    (slot 3) (.hyp (Or.inl rfl))

private theorem negative_at_selection {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (sameBound : vn 8 = vo 8)
    (Sel Operand : Fin m)
    (hSel : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 0) Sel))
    (hOperand : Derives Γ (substituted p.w (vo 8) Sel p.a p.f p.z p.B p.N Operand)) : Derives Γ (p.goal test) := by
  have record := negative_at_records h.zf Reln p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SOld p.j
    p.N p.n (sv 3) p.ParentOld vo uo cv sv h.parentOld h.compiler h.shell
  let E := guardData Reln (old 4 p.w) (old 4 (uo 7)) (old 4 (vo 9)) (old 4 p.alpha)
    (old 4 p.f) (old 4 p.z) (old 4 p.B) (old 4 (p.P 0)) (old 4 (cv 1)) (old 4 (cv 3))
    (old 4 (cv 4)) (old 4 (sv 1)) (old 4 (sv 2)) (old 4 (uo 8)) (slot 4)
  apply HornBinderRules.eliminate_many 4 E _ (.conjR (.conjR (.conjR record)))
  apply of_eq (NegativeArgs.goal_rename test p (old 4)).symm
  exact negative_at_guards (h.in_body E) (congrArg (old 4) sameBound) (old 4 Sel) (old 4 Operand)
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (old 4)) (HornBinderRules.under_body 4 hSel E))
    (of_eq (substituted_rename _ _ _ _ _ _ _ _ _ (old 4)) (HornBinderRules.under_body 4 hOperand E))
    (slot 4) (.hyp (Or.inl rfl))

private theorem negative_at_table {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (sameBound : vn 8 = vo 8)
    (Sel : Fin m)
    (hSel : Derives Γ (ForcingReflexiveImages.replacement p.w p.f p.z p.B (p.v 9) p.j (p.P 0) Sel)) :
    Derives Γ (p.goal test) := by
  have images := Derives.conjL (.conjR h.parentOld)
  have lists := SyntaxMixedImageCodePairs.term_lists p.w (vo 6) (vo 7) p.a p.f p.z p.B (vo 8) (vo 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have selected := ForcingReflexiveImages.target_type p.w p.f p.z p.B (p.v 9) p.j (p.P 0) Sel hSel
  have query := SyntaxMixedFormulaOutputInduction.actual_exists h.zf p.w (vo 8) Sel p.a p.f p.z p.B p.N
    (.conjL (.conjL h.parentOld)) (.conjI h.childType (.conjI (.conjL lists) selected))
  let E := substituted (old 1 p.w) (old 1 (vo 8)) (old 1 Sel) (old 1 p.a) (old 1 p.f)
    (old 1 p.z) (old 1 p.B) (old 1 p.N) (slot 1 0)
  apply HornBinderRules.eliminate_many 1 E _ query
  apply of_eq (NegativeArgs.goal_rename test p (old 1)).symm
  exact negative_at_selection (h.in_body E) (congrArg (old 1) sameBound) (old 1 Sel) (slot 1 0)
    (of_eq (ForcingReflexiveImages.replacement_rename _ _ _ _ _ _ _ _ (old 1)) (HornBinderRules.under_body 1 hSel E))
    (.hyp (Or.inl rfl))

private theorem transfer_negative_opened {k m} {Γ : Context m} {test : Formula 1}
    {Reln : Source.Formula (k+2)} {p : NegativeArgs m} {cv : Fin 5 → Fin m} {sv : Fin 4 → Fin m}
    {vo vn : Fin 10 → Fin m} {uo un : Fin 9 → Fin m}
    (h : NegativeOpened Γ test Reln p cv sv vo vn uo un) (sameBound : vn 8 = vo 8) :
    Derives Γ (p.goal test) := by
  have src := Derives.conjL h.parentOld
  have term := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))
  have sel := ForcingReflexiveImages.exists_replacement h.zf p.w p.f p.z p.B (p.v 9) p.j (p.P 0)
    (.conjL src) h.baseType term
  let E := ForcingReflexiveImages.replacement (old 1 p.w) (old 1 p.f) (old 1 p.z) (old 1 p.B)
    (old 1 (p.v 9)) (old 1 p.j) (old 1 (p.P 0)) (slot 1 0)
  apply HornBinderRules.eliminate_many 1 E _ sel
  apply of_eq (NegativeArgs.goal_rename test p (old 1)).symm
  exact negative_at_table (h.in_body E) (congrArg (old 1) sameBound) (slot 1 0) (.hyp (Or.inl rfl))


private theorem with_negative_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (w a alpha f j N n : Fin m) (target : Formula m)
    (hFull : Derives Γ (ForcingNegCode.compiled Reln w a alpha f j N n))
    (consume : ∀ {l} {Δ : Context l} (rho : Fin m → Fin l) (cv : Fin 5 → Fin l) (sv : Fin 4 → Fin l),
      ZFContext.Evidence Δ → (∀ {p}, Derives Γ p → Derives Δ (p.rename rho)) →
      Derives Δ (ForcingNegCode.data Reln (rho w) (rho a) (rho alpha) (rho f) (rho j) (rho N) (rho n) cv) →
      Derives Δ (ForcingNegCode.shellData (rho w) (rho a) (rho alpha) (rho f) (cv 3) (cv 4) (cv 2) (rho n) sv) →
      Derives Δ (target.rename rho)) : Derives Γ target := by
  let E := ForcingNegCode.body Reln w a alpha f j N n
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ (.conjR hFull)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let F := ForcingNegCode.shellBody (old 5 w) (old 5 a) (old 5 alpha) (old 5 f)
    (slot 5 3) (slot 5 4) (slot 5 2) (old 5 n)
  let Ξ := Context.add F (raisedContext 4 Δ)
  have shell := Derives.conjR (.conjR (.conjR (.conjR hE)))
  apply HornBinderRules.eliminate_many 4 F _ shell
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  let rho := fun i : Fin m => old 4 (old 5 i)
  have move {q : Formula m} (hq : Derives Γ q) : Derives Ξ (q.rename rho) :=
    of_eq (rename_comp q (old 5) (old 4))
      (HornBinderRules.under_body 4 (HornBinderRules.under_body 5 hq E) F)
  have hc := of_eq (ForcingNegCode.data_rename Reln (old 5 w) (old 5 a) (old 5 alpha)
    (old 5 f) (old 5 j) (old 5 N) (old 5 n) (slot 5) (old 4)) (HornBinderRules.under_body 4 hE F)
  exact of_eq (rename_comp target (old 5) (old 4)).symm
    (consume rho (fun i => old 4 (slot 5 i)) (slot 4)
      (HornBinderRules.zf_body 4 (HornBinderRules.zf_body 5 hZ E) F) move hc hF)

private theorem input_with_constructor {m} {Γ : Context m}
    (w z a f alpha b A B t R S n x Parent : Fin m)
    (hf : Derives Γ (ForcingFreshParentOpening.frame w z a f alpha b A B t R S n Parent))
    (hc : Derives Γ (singleCode 9 w x n)) :
    Derives Γ (ForcingFreshParentOpening.input w z a f alpha b A B t R S n x Parent) := by
  refine .conjI (.conjL hf) ?_
  have h := Derives.conjR hf
  refine .conjI (.conjL h) ?_
  have h := Derives.conjR h
  refine .conjI (.conjL h) ?_
  have h := Derives.conjR h
  refine .conjI (.conjL h) ?_
  have h := Derives.conjR h
  refine .conjI (.conjL h) ?_
  have h := Derives.conjR h
  refine .conjI (.conjL h) ?_
  have h := Derives.conjR h
  exact .conjI (.conjL h) (.conjI hc (.conjR h))

private def negativeFrames {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (p : NegativeArgs m) : Formula m :=
  (ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.R p.S p.j p.QOld (p.P 2) p.SOld p.Old p.v).conj
    ((ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.R p.S p.j p.QNew (p.P 1) p.SNew p.New p.v).conj
    ((ForcingFreshParentOpening.frame p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SOld p.n p.ParentOld).conj
    ((ForcingFreshParentOpening.frame p.w p.z p.a p.f p.alpha p.b p.A p.B (p.P 0) p.R p.SNew p.n p.ParentNew).conj
    ((ForcingNegCode.compiled Reln p.w p.a p.alpha p.f p.j p.N p.n).conj
    ((FormulaCodeSyntax.formulaCode p.w p.N p.a p.f).conj
    ((SyntaxWeakenFreeSyntax.weakened p.w p.z p.b p.B p.G (p.ctx 3)).conj
    ((InternalProofBackground.implication test p.w p.z p.b p.G p.ParentOld).conj
    ((FormulaCodeSyntax.formulaCode p.w p.Extra p.z p.B).conj
    ((ForcingProofContext.layoutData p.w p.z p.B p.Extra p.Pre p.H p.ctx).conj
    ((SyntaxNumeralSyntax.numeral 0 p.z).conj
    ((SyntaxNumeralSyntax.numeral 1 p.A1).conj
    ((SyntaxNumeralSyntax.numeral 2 p.A2).conj
    ((SyntaxNumeralSyntax.numeral 3 p.A3).conj
    ((SyntaxNumeralSyntax.numeral (k+2) p.f).conj
    ((SyntaxNumeralSyntax.numeral k p.i).conj
    (ForcingPreorderLeaves.data test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.B p.C p.Bound (p.v 9) p.Refl p.Pre p.raw p.Gb p.H p.U
      p.F p.P p.N0 p.D))))))))))))))))

set_option maxHeartbeats 1800000 in
private theorem negative_from_input {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (p : NegativeArgs m)
    (hi : Derives Γ (negativeFrames test Reln p)) : Derives Γ (p.goal test) := by
  have oldFrame := Derives.conjL hi
  have rest := Derives.conjR hi
  have newFrame := Derives.conjL rest
  have rest := Derives.conjR rest
  have sourceOld := Derives.conjL rest
  have rest := Derives.conjR rest
  have sourceNew := Derives.conjL rest
  have rest := Derives.conjR rest
  have full := Derives.conjL rest
  have rest := Derives.conjR rest
  have childType := Derives.conjL rest
  have rest := Derives.conjR rest
  have weak := Derives.conjL rest
  have rest := Derives.conjR rest
  have oldProof := Derives.conjL rest
  have rest := Derives.conjR rest
  have extraType := Derives.conjL rest
  have rest := Derives.conjR rest
  have layout := Derives.conjL rest
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
  have carrier := Derives.conjL rest
  have rest := Derives.conjR rest
  have row := rest
  have images := Derives.conjL oldFrame
  have lists := SyntaxMixedImageCodePairs.term_lists p.w (p.v 6) (p.v 7) p.a p.f p.z p.B (p.v 8) (p.v 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have baseType := Derives.conjR lists
  have oldTable := Derives.conjL (.conjR (.conjR oldFrame))
  have newTable := Derives.conjL (.conjR (.conjR newFrame))
  apply with_negative_records hZ Reln p.w p.a p.alpha p.f p.j p.N p.n _ full
  intro l Δ rho cv sv zf move compiler shell
  let p' := p.map rho
  have frameOld : Derives Δ (ForcingWeakenedOverwrite.frame p'.w p'.a p'.f p'.z p'.b p'.B
      p'.R p'.S p'.j p'.QOld (p'.P 2) p'.SOld p'.Old p'.v) := by
    simpa only [p', NegativeArgs.map, ForcingWeakenedOverwrite.frame_rename] using move oldFrame
  have frameNew : Derives Δ (ForcingWeakenedOverwrite.frame p'.w p'.a p'.f p'.z p'.b p'.B
      p'.R p'.S p'.j p'.QNew (p'.P 1) p'.SNew p'.New p'.v) := by
    simpa only [p', NegativeArgs.map, ForcingWeakenedOverwrite.frame_rename] using move newFrame
  have bodyCode : Derives Δ (singleCode 9 p'.w (sv 3) p'.n) :=
    .conjL (.conjR (.conjR (.conjR (.conjR shell))))
  have srcOld : Derives Δ (ForcingFreshParentOpening.frame p'.w p'.z p'.a p'.f p'.alpha p'.b p'.A
      p'.B (p'.P 0) p'.R p'.SOld p'.n p'.ParentOld) := by
    simpa only [p', NegativeArgs.map, ForcingFreshParentOpening.frame_rename] using move sourceOld
  have srcNew : Derives Δ (ForcingFreshParentOpening.frame p'.w p'.z p'.a p'.f p'.alpha p'.b p'.A
      p'.B (p'.P 0) p'.R p'.SNew p'.n p'.ParentNew) := by
    simpa only [p', NegativeArgs.map, ForcingFreshParentOpening.frame_rename] using move sourceNew
  have hOld := input_with_constructor p'.w p'.z p'.a p'.f p'.alpha p'.b p'.A p'.B (p'.P 0)
    p'.R p'.SOld p'.n (sv 3) p'.ParentOld srcOld bodyCode
  have hNew := input_with_constructor p'.w p'.z p'.a p'.f p'.alpha p'.b p'.A p'.B (p'.P 0)
    p'.R p'.SNew p'.n (sv 3) p'.ParentNew srcNew bodyCode
  apply of_eq (NegativeArgs.goal_rename test p rho).symm
  apply with_overwrites zf p'.w p'.z p'.a p'.f p'.alpha p'.b p'.A p'.B (p'.P 0) p'.R p'.S p'.j
    p'.n (sv 3) p'.ParentOld p'.ParentNew p'.QOld p'.QNew (p'.P 2) (p'.P 1)
    p'.SOld p'.SNew p'.Old p'.New p'.v _ (.conjI frameOld hOld) (.conjI frameNew hNew)
  intro t Ξ sigma vo vn uo un zf' move' sameBound oldFree newFree parentOld parentNew
  let q := p'.map sigma
  have raise {r : Formula m} (hr : Derives Γ r) : Derives Ξ (r.rename (fun i => sigma (rho i))) :=
    of_eq (rename_comp r rho sigma) (move' (move hr))
  have opened : NegativeOpened Ξ test Reln q (fun i => sigma (cv i)) (fun i => sigma (sv i)) vo vn uo un := by
    refine ⟨zf', parentOld, parentNew, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [q, p', NegativeArgs.map, ForcingNegCode.data_rename] using move' compiler
    · simpa only [q, p', NegativeArgs.map, ForcingNegCode.shellData_rename] using move' shell
    · simpa only [q, p', NegativeArgs.map, ForcingNegCode.compiled_rename] using raise full
    · simpa only [q, p', NegativeArgs.map, FormulaCodeSyntax.formulaCode_rename] using raise childType
    · simpa only [q, p', NegativeArgs.map, SyntaxWeakenFreeSyntax.weakened_rename] using raise weak
    · simpa only [q, p', NegativeArgs.map, InternalProofBackground.implication_rename] using raise oldProof
    · simpa only [q, p', NegativeArgs.map, FormulaCodeSyntax.formulaCode_rename] using raise extraType
    · simpa only [q, p', NegativeArgs.map, ForcingProofContext.layoutData_rename] using raise layout
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise zero
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise one
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise two
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise three
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise free
    · simpa only [q, p', NegativeArgs.map, SyntaxNumeralSyntax.numeral_rename] using raise carrier
    · simpa only [q, p', NegativeArgs.map, ForcingPreorderLeaves.data_rename] using raise row
    · simpa only [q, p', NegativeArgs.map, oldFree, ForcingReflexiveImages.replacement_rename] using raise oldTable
    · simpa only [q, p', NegativeArgs.map, newFree, ForcingReflexiveImages.replacement_rename] using raise newTable
    · simpa only [q, p', NegativeArgs.map, SyntaxMixedImageCodeSyntax.termList_rename] using raise baseType
  exact of_eq (NegativeArgs.goal_rename test p' sigma).symm (transfer_negative_opened opened sameBound)

/-- The two original parent queries, complete negative compiler, overwrite
frames on one weak base table, and the common canonical context. -/
def negativeFramesInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) : Formula m :=
  negativeFrames test Reln ⟨w, z, a, f, alpha, b, A, B, R, S, j, N, n, ParentOld, ParentNew, A1, A2, A3, C, Bound, Refl, Pre, i, G, Extra, QOld, QNew, SOld,
      SNew, Old, New, v, raw, Gb, H, U, F, P, N0, D, ctx⟩

theorem transfer_negative_from_frames {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m)
    (hi : Derives Γ (negativeFramesInput test Reln w z a f alpha b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld
      SNew Old New v raw Gb H U F P N0 D ctx)) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) :=
  negative_from_input hZ test Reln ⟨w, z, a, f, alpha, b, A, B, R, S, j, N, n, ParentOld, ParentNew, A1, A2, A3, C, Bound, Refl, Pre, i, G, Extra, QOld, QNew, SOld,
      SNew, Old, New, v, raw, Gb, H, U, F, P, N0, D, ctx⟩ hi

theorem transfer_negative_from_frames_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence
        ((negativeFramesInput test Reln w z a f alpha b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld
      SNew Old New v raw Gb H U F P N0 D ctx).imp
          (InternalProofBackground.implication test w z b G ParentNew)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact transfer_negative_from_frames (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z a f alpha b A B R S j N n
      ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld SNew Old New v raw Gb H U F P N0 D ctx
      (.hyp (Or.inl rfl))


/-- The existential branch starts with the complete original compiler and
the two actual parent queries. Its source body is chosen by that compiler. -/
def existentialCompiledInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) : Formula m :=
  (ForcingWeakenedOverwrite.frame w a f z b B R S j QOld (P 2) SOld Old v).conj
    ((ForcingWeakenedOverwrite.frame w a f z b B R S j QNew (P 1) SNew New v).conj
    ((ForcingFreshParentOpening.frame w z a f alpha b A B (P 0) R SOld n ParentOld).conj
    ((ForcingFreshParentOpening.frame w z a f alpha b A B (P 0) R SNew n ParentNew).conj
    ((ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n).conj
    (existentialContextData test Reln w z f alpha beta gamma b B j N ParentOld A1 A2 A3 C Bound (v 9) Refl Pre i G Extra Old
      New raw Gb H U F P N0 D ctx)))))

set_option maxHeartbeats 1500000 in
theorem transfer_existential_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m)
    (hi : Derives Γ (existentialCompiledInput test Reln Dom w z a f alpha beta gamma b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G
      Extra QOld QNew SOld SNew Old New v raw Gb H U F P N0 D ctx)) :
    Derives Γ (InternalProofBackground.implication test w z b G ParentNew) := by
  have oldFrame := Derives.conjL hi
  have rest := Derives.conjR hi
  have newFrame := Derives.conjL rest
  have rest := Derives.conjR rest
  have oldParent := Derives.conjL rest
  have rest := Derives.conjR rest
  have newParent := Derives.conjL rest
  have rest := Derives.conjR rest
  have full := Derives.conjL rest
  have context := Derives.conjR rest
  let E := ForcingExistCode.body Reln Dom w a alpha beta gamma f j N n
  let Δ := Context.add E (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 E _ (.conjR full)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  let FShell := ForcingExistCode.shellBody (old 8 w) (old 8 a) (old 8 alpha) (old 8 beta) (old 8 gamma)
    (old 8 f) (slot 8 2) (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 n)
  let Ξ := Context.add FShell (raisedContext 7 Δ)
  have shell := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hE))))))
  apply HornBinderRules.eliminate_many 7 FShell _ shell
  have hF : Derives Ξ FShell := .hyp (Or.inl rfl)
  let rho := fun i : Fin m => old 7 (old 8 i)
  let cv := fun i : Fin 8 => old 7 (slot (m := m) 8 i)
  let sv := slot (m := m+8) 7
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Ξ (q.rename rho) :=
    of_eq (rename_comp q (old 8) (old 7))
      (HornBinderRules.under_body 7 (HornBinderRules.under_body 8 hq E) FShell)
  have compiler := of_eq (ForcingExistCode.data_rename Reln Dom (old 8 w) (old 8 a) (old 8 alpha)
    (old 8 beta) (old 8 gamma) (old 8 f) (old 8 j) (old 8 N) (old 8 n) (slot 8) (old 7))
    (HornBinderRules.under_body 7 hE FShell)
  have ctor : Derives Ξ (singleCode 9 (rho w) (sv 6) (rho n)) :=
    .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hF)))))))
  have srcOld : Derives Ξ (ForcingFreshParentOpening.frame (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A)
      (rho B) (rho (P 0)) (rho R) (rho SOld) (rho n) (rho ParentOld)) := by
    simpa only [ForcingFreshParentOpening.frame_rename] using lift oldParent
  have srcNew : Derives Ξ (ForcingFreshParentOpening.frame (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A)
      (rho B) (rho (P 0)) (rho R) (rho SNew) (rho n) (rho ParentNew)) := by
    simpa only [ForcingFreshParentOpening.frame_rename] using lift newParent
  have hOld := input_with_constructor (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho (P 0))
      (rho R) (rho SOld) (rho n) (sv 6) (rho ParentOld) srcOld ctor
  have hNew := input_with_constructor (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho (P 0))
      (rho R) (rho SNew) (rho n) (sv 6) (rho ParentNew) srcNew ctor
  have wOld : Derives Ξ (ForcingWeakenedOverwrite.frame (rho w) (rho a) (rho f) (rho z) (rho b) (rho B) (rho R) (rho S)
      (rho j) (rho QOld) (rho (P 2)) (rho SOld) (rho Old) (fun i => rho (v i))) := by
    simpa only [ForcingWeakenedOverwrite.frame_rename] using lift oldFrame
  have wNew : Derives Ξ (ForcingWeakenedOverwrite.frame (rho w) (rho a) (rho f) (rho z) (rho b) (rho B) (rho R) (rho S)
      (rho j) (rho QNew) (rho (P 1)) (rho SNew) (rho New) (fun i => rho (v i))) := by
    simpa only [ForcingWeakenedOverwrite.frame_rename] using lift newFrame
  have hContext : Derives Ξ (existentialContextData test Reln (rho w) (rho z) (rho f) (rho alpha) (rho beta) (rho gamma)
      (rho b) (rho B) (rho j) (rho N) (rho ParentOld) (rho A1) (rho A2) (rho A3) (rho C) (rho Bound) (rho (v 9)) (rho Refl)
      (rho Pre) (rho i) (rho G) (rho Extra) (rho Old) (rho New) (fun i => rho (raw i)) (fun i => rho (Gb i))
      (fun i => rho (H i)) (fun i => rho (U i)) (fun i => rho (F i)) (fun i => rho (P i)) (fun i => rho (N0 i))
      (fun i => rho (D i)) (fun i => rho (ctx i))) := by
    simpa only [existentialContextData, Formula.rename, successor_rename, FormulaCodeSyntax.formulaCode_rename,
      SyntaxWeakenFreeSyntax.weakened_rename, InternalProofBackground.implication_rename, ForcingProofContext.layoutData_rename,
      SyntaxNumeralSyntax.numeral_rename, ForcingPreorderLeaves.data_rename, ForcingReflexiveImages.replacement_rename]
      using lift context
  have hZ' := HornBinderRules.zf_body 7 (HornBinderRules.zf_body 8 hZ E) FShell
  have result := transfer_existential_from_frames hZ' test Reln Dom (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho beta)
      (rho gamma) (rho b) (rho A) (rho B) (rho R) (rho S) (rho j) (rho N) (rho n) (sv 6) (rho ParentOld) (rho ParentNew)
      (rho A1) (rho A2) (rho A3) (rho C) (rho Bound) (rho (v 9)) (rho Refl) (rho Pre) (rho i) (rho G) (rho Extra) (rho QOld)
      (rho QNew) (rho SOld) (rho SNew) (rho Old) (rho New) (fun i => rho (v i)) cv sv (fun i => rho (raw i))
      (fun i => rho (Gb i)) (fun i => rho (H i)) (fun i => rho (U i)) (fun i => rho (F i)) (fun i => rho (P i))
      (fun i => rho (N0 i)) (fun i => rho (D i)) (fun i => rho (ctx i))
    (.conjI (.conjI wOld hOld) (.conjI (.conjI wNew hNew) (.conjI compiler (.conjI hF hContext))))
  simpa only [rename_comp, rho, InternalProofBackground.implication_rename] using result

theorem transfer_existential_compiled_kernel_certificate {k m}
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f alpha beta gamma b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra
      QOld QNew SOld SNew Old New : Fin m)
    (v : Fin 10 → Fin m) (raw : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N0 : Fin 5 → Fin m) (D : Fin 3 → Fin m) (ctx : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence
        ((existentialCompiledInput test Reln Dom w z a f alpha beta gamma b A B R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G
            Extra QOld QNew SOld SNew Old New v raw Gb H U F P N0 D ctx).imp
          (InternalProofBackground.implication test w z b G ParentNew)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact transfer_existential_compiled (ZFContext.add (ZFContext.source_ZF m) _) test Reln Dom w z a f alpha beta gamma b A B
      R S j N n ParentOld ParentNew A1 A2 A3 C Bound Refl Pre i G Extra QOld QNew SOld SNew Old New v raw Gb H U F P N0 D ctx
      (.hyp (Or.inl rfl))


private structure ModalRunArgs (m : Nat) where
  w : Fin m
  z : Fin m
  a : Fin m
  f : Fin m
  j : Fin m
  b : Fin m
  B : Fin m
  R : Fin m
  S : Fin m
  T : Fin m
  SOld : Fin m
  SNew : Fin m
  A1 : Fin m
  A2 : Fin m
  A3 : Fin m
  K : Fin m
  Extra : Fin m
  raw : Fin 16 → Fin m
  v : Fin 10 → Fin m
  C : Fin 2 → Fin m
  Refl : Fin 2 → Fin m
  Pre : Fin 2 → Fin m
  U0 : Fin 2 → Fin m
  P : Fin 2 → Fin 3 → Fin m
  x : Fin 48 → Fin m
  oldCtx : Fin 6 → Fin m

private def ModalRunArgs.map {m l} (p : ModalRunArgs m) (rho : Fin m → Fin l) : ModalRunArgs l :=
  ⟨rho p.w, rho p.z, rho p.a, rho p.f, rho p.j, rho p.b, rho p.B, rho p.R, rho p.S, rho p.T, rho p.SOld, rho p.SNew,
      rho p.A1, rho p.A2, rho p.A3, rho p.K, rho p.Extra, (fun i => rho (p.raw i)), (fun i => rho (p.v i)),
      (fun i => rho (p.C i)), (fun i => rho (p.Refl i)), (fun i => rho (p.Pre i)), (fun i => rho (p.U0 i)),
      (fun s i => rho (p.P s i)), (fun i => rho (p.x i)), (fun i => rho (p.oldCtx i))⟩

private def ModalRunArgs.aux {k m : Nat} (p : ModalRunArgs m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termList p.w p.a p.z p.b p.T).conj
    ((SyntaxNumeralSyntax.numeral (k+1) p.j).conj
      ((ForcingReflexiveImages.replacement p.w p.f p.z p.b p.S p.j (p.P 0 2) p.SOld).conj
        (ForcingReflexiveImages.replacement p.w p.f p.z p.b p.S p.j (p.P 0 1) p.SNew)))

private theorem ModalRunArgs.aux_rename {k m l} (p : ModalRunArgs m) (rho : Fin m → Fin l) :
    (p.aux (k := k)).rename rho = (p.map rho).aux (k := k) := by
  simp only [ModalRunArgs.aux, ModalRunArgs.map, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename,
    SyntaxNumeralSyntax.numeral_rename, ForcingReflexiveImages.replacement_rename]

private def ModalRunArgs.input {k m} (p : ModalRunArgs m) (test : Formula 1) (Reln : Source.Formula (k+2)) : Formula m :=
  (ForcingGlobalWeakening.input test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.B p.R p.S p.K p.Extra p.raw p.v p.C p.Refl p.Pre
      p.U0 p.P p.x p.oldCtx).conj (p.aux (k := k))

/-- The existing global preorder and layout input, typed independent parent
bound table, condition slot, and the two actual original replacements. -/
def globalModalInput {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) : Formula m :=
  ModalRunArgs.input ⟨w, z, a, f, j, b, B, R, S, T, SOld, SNew, A1, A2, A3, K, Extra, raw, v, C, Refl, Pre, U0, P, x, oldCtx⟩ test Reln

private def ModalRunArgs.live {k m} (p : ModalRunArgs m) (test : Formula 1) (Reln : Source.Formula (k+2))
    (y : Fin 7 → Fin m) (r g Tp Old New : Fin m) : Formula m :=
  let vv := ForcingWeakenedImages.withBound p.v r g Tp
  (ForcingGlobalWeakening.data test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.B p.R p.S p.K p.Extra p.raw p.v p.C p.Refl p.Pre
      p.U0 p.P p.x p.oldCtx y).conj
    ((ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.T p.S p.j (p.P 0 2) (p.P 1 2) p.SOld Old vv).conj
      ((ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.T p.S p.j (p.P 0 1) (p.P 1 1) p.SNew New vv).conj
        (SyntaxNumeralSyntax.numeral (k+1) p.j)))


set_option maxHeartbeats 2000000 in
private theorem with_global_runtime {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (p : ModalRunArgs m)
    (hi : Derives Γ (p.input test Reln)) (target : Formula m)
    (consume : ∀ {l} {Δ : Context l} (rho : Fin m → Fin l) (y : Fin 7 → Fin l) (r g Tp Old New : Fin l),
      ZFContext.Evidence Δ → (∀ {q}, Derives Γ q → Derives Δ (q.rename rho)) →
      Derives Δ ((p.map rho).live test Reln y r g Tp Old New) → Derives Δ (target.rename rho)) :
    Derives Γ target := by
  let E := ForcingGlobalWeakening.body test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.B p.R p.S p.K p.Extra p.raw p.v p.C p.Refl
      p.Pre p.U0 p.P p.x p.oldCtx
  let Γ7 := Context.add E (raisedContext 7 Γ)
  apply HornBinderRules.eliminate_many 7 E _ (ForcingGlobalWeakening.produce hZ test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.b p.B
      p.R p.S p.K p.Extra p.raw p.v p.C p.Refl p.Pre p.U0 p.P p.x p.oldCtx (.conjL hi))
  let p7 := p.map (old 7)
  have hg7 : Derives Γ7 E := .hyp (Or.inl rfl)
  have hZ7 := HornBinderRules.zf_body 7 hZ E
  have aux7 := of_eq (ModalRunArgs.aux_rename (k := k) p (old 7)) (HornBinderRules.under_body 7 (.conjR hi) E)
  have fresh := Derives.conjL (.conjR (.conjL hg7))
  have images := Derives.conjL (.conjR (.conjR (.conjL fresh)))
  have hw := Derives.conjL (.conjL images)
  have lists := SyntaxMixedImageCodePairs.term_lists p7.w (p7.v 6) (p7.v 7) p7.z p7.f p7.z p7.B (p7.v 8) (p7.v 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have renamedQ := Derives.conjL (.conjR (.conjR (.conjR fresh)))
  have renamedP := Derives.conjL (.conjR (.conjR (.conjR (.conjR fresh))))
  have hq := SyntaxRenameTermTyping.target_term p7.w (p7.v 2) (p7.v 3) p7.z p7.b p7.z p7.B (p7.P 0 1) (p7.P 1 1) renamedQ
  have hp := SyntaxRenameTermTyping.target_term p7.w (p7.v 2) (p7.v 3) p7.z p7.b p7.z p7.B (p7.P 0 2) (p7.P 1 2) renamedP
  have oldExists := ForcingReflexiveImages.exists_replacement hZ7 p7.w p7.f p7.z p7.B (p7.v 9) p7.j (p7.P 1 2)
    hw (.conjR lists) hp
  have newExists := ForcingReflexiveImages.exists_replacement hZ7 p7.w p7.f p7.z p7.B (p7.v 9) p7.j (p7.P 1 1)
    hw (.conjR lists) hq
  let D := ForcingWeakenedImages.boundBody p7.w p7.a p7.f p7.z p7.b p7.B p7.T p7.S p7.v
  let Γ10 := Context.add D (raisedContext 3 Γ7)
  apply HornBinderRules.eliminate_many 3 D _ (ForcingWeakenedImages.rebase_bound hZ7 p7.w p7.z p7.a p7.f p7.z
    p7.b p7.B p7.R p7.S p7.T p7.v images (.conjL aux7))
  let p10 := p7.map (old 3)
  have hD : Derives Γ10 D := .hyp (Or.inl rfl)
  have old10 := of_eq (ForcingReflexiveImages.existsReplacement_rename p7.w p7.f p7.z p7.B (p7.v 9) p7.j (p7.P 1 2) (old 3))
    (HornBinderRules.under_body 3 oldExists D)
  have new10 := of_eq (ForcingReflexiveImages.existsReplacement_rename p7.w p7.f p7.z p7.B (p7.v 9) p7.j (p7.P 1 1) (old 3))
    (HornBinderRules.under_body 3 newExists D)
  let O := ForcingReflexiveImages.replacement (old 1 p10.w) (old 1 p10.f) (old 1 p10.z) (old 1 p10.B)
    (old 1 (p10.v 9)) (old 1 p10.j) (old 1 (p10.P 1 2)) (slot 1 0)
  let Γ11 := Context.add O (raisedContext 1 Γ10)
  apply HornBinderRules.eliminate_many 1 O _ old10
  have hO : Derives Γ11 O := .hyp (Or.inl rfl)
  have new11 := of_eq (ForcingReflexiveImages.existsReplacement_rename p10.w p10.f p10.z p10.B (p10.v 9) p10.j
    (p10.P 1 1) (old 1)) (HornBinderRules.under_body 1 new10 O)
  let N := ForcingReflexiveImages.replacement (old 1 (old 1 p10.w)) (old 1 (old 1 p10.f)) (old 1 (old 1 p10.z))
    (old 1 (old 1 p10.B)) (old 1 (old 1 (p10.v 9))) (old 1 (old 1 p10.j)) (old 1 (old 1 (p10.P 1 1))) (slot 1 0)
  let Γ12 := Context.add N (raisedContext 1 Γ11)
  apply HornBinderRules.eliminate_many 1 N _ new11
  have hN : Derives Γ12 N := .hyp (Or.inl rfl)
  let after10 := fun i : Fin ((m+7)+3) => old 1 (old 1 i)
  let after7 := fun i : Fin (m+7) => after10 (old 3 i)
  let rho := fun i : Fin m => after7 (old 7 i)
  let q := p.map rho
  let y := fun i : Fin 7 => after7 (slot 7 i)
  let r := after10 (slot 3 0)
  let g := after10 (slot 3 1)
  let Tp := after10 (slot 3 2)
  let Old : Fin ((((m+7)+3)+1)+1) := old 1 (slot 1 0)
  let New : Fin ((((m+7)+3)+1)+1) := slot 1 0
  let vv := ForcingWeakenedImages.withBound q.v r g Tp
  have move10 {u : Formula ((m+7)+3)} (hu : Derives Γ10 u) : Derives Γ12 (u.rename after10) :=
    of_eq (rename_comp u (old 1) (old 1))
      (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hu O) N)
  have move7 {u : Formula (m+7)} (hu : Derives Γ7 u) : Derives Γ12 (u.rename after7) :=
    of_eq (rename_comp u (old 3) after10) (move10 (HornBinderRules.under_body 3 hu D))
  have move {u : Formula m} (hu : Derives Γ u) : Derives Γ12 (u.rename rho) :=
    of_eq (rename_comp u (old 7) after7) (move7 (HornBinderRules.under_body 7 hu E))
  have global : Derives Γ12 (ForcingGlobalWeakening.data test Reln q.w q.z q.A1 q.A2 q.A3 q.f q.b q.B q.R q.S q.K q.Extra
      q.raw q.v q.C q.Refl q.Pre q.U0 q.P q.x q.oldCtx y) := by
    simpa only [E, ForcingGlobalWeakening.body, ForcingGlobalWeakening.data_rename, q, y, rho, ModalRunArgs.map] using move7 hg7
  have parent : Derives Γ12 (ForcingWeakenedImages.data q.w q.a q.f q.z q.b q.B q.T q.S vv) := by
    simpa only [D, ForcingWeakenedImages.boundBody, ForcingWeakenedImages.data_rename, ForcingWeakenedImages.withBound_map,
      vv, q, rho, after7, r, g, Tp, p7, ModalRunArgs.map] using move10 hD
  have selectedOld : Derives Γ12 (ForcingReflexiveImages.replacement q.w q.f q.z q.B (q.v 9) q.j (q.P 1 2) Old) := by
    simpa only [O, q, rho, after7, after10, p10, p7, Old, ModalRunArgs.map, ForcingReflexiveImages.replacement_rename] using
      HornBinderRules.under_body 1 hO N
  have aux := of_eq (ModalRunArgs.aux_rename (k := k) p rho) (move (.conjR hi))
  have freshNew := Derives.conjL (.conjR (.conjL global))
  have hqn := Derives.conjL (.conjR (.conjR (.conjR freshNew)))
  have hpn := Derives.conjL (.conjR (.conjR (.conjR (.conjR freshNew))))
  have oldFrame : Derives Γ12 (ForcingWeakenedOverwrite.frame q.w q.a q.f q.z q.b q.B q.T q.S q.j
      (q.P 0 2) (q.P 1 2) q.SOld Old vv) :=
    .conjI parent (.conjI (.conjL (.conjR (.conjR aux))) (.conjI selectedOld hpn))
  have newFrame : Derives Γ12 (ForcingWeakenedOverwrite.frame q.w q.a q.f q.z q.b q.B q.T q.S q.j
      (q.P 0 1) (q.P 1 1) q.SNew New vv) :=
    .conjI parent (.conjI (.conjR (.conjR (.conjR aux))) (.conjI hN hqn))
  have live : Derives Γ12 (q.live test Reln y r g Tp Old New) :=
    .conjI global (.conjI oldFrame (.conjI newFrame (.conjL (.conjR aux))))
  have hZ10 := HornBinderRules.zf_body 3 hZ7 D
  have hZ12 := HornBinderRules.zf_body 1 (HornBinderRules.zf_body 1 hZ10 O) N
  have result := consume rho y r g Tp Old New hZ12 move live
  simpa only [rho, after7, after10, rename_comp] using result


private theorem ModalRunArgs.live_rename {k m l} (p : ModalRunArgs m) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (y : Fin 7 → Fin m) (r g Tp Old New : Fin m) (rho : Fin m → Fin l) :
    (p.live test Reln y r g Tp Old New).rename rho =
      (p.map rho).live test Reln (fun i => rho (y i)) (rho r) (rho g) (rho Tp) (rho Old) (rho New) := by
  simp only [ModalRunArgs.live, ModalRunArgs.map, Formula.rename, ForcingGlobalWeakening.data_rename,
    ForcingWeakenedOverwrite.frame_rename, ForcingWeakenedImages.withBound_map, SyntaxNumeralSyntax.numeral_rename]

private def ModalRunArgs.row {m} (p : ModalRunArgs m) : Fin 24 → Fin m := fun i => p.x (i.addNat 24)

private structure ModalLive {k m} (Γ : Context m) (p : ModalRunArgs m) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (y : Fin 7 → Fin m) (r g Tp Old New : Fin m) : Prop where
  oldFrame : Derives Γ (ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.T p.S p.j
    (p.P 0 2) (p.P 1 2) p.SOld Old (ForcingWeakenedImages.withBound p.v r g Tp))
  newFrame : Derives Γ (ForcingWeakenedOverwrite.frame p.w p.a p.f p.z p.b p.B p.T p.S p.j
    (p.P 0 1) (p.P 1 1) p.SNew New (ForcingWeakenedImages.withBound p.v r g Tp))
  source : ∀ (alpha n S Parent : Fin m),
    Derives Γ (successor alpha p.a) →
    Derives Γ (substituted p.w p.T S p.a p.f p.z p.b n Parent) →
    Derives Γ (ForcingFreshParentOpening.frame p.w p.z p.a p.f alpha p.b (p.C 1) p.B
      (p.P 1 0) p.T S n Parent)
  weak : Derives Γ (SyntaxWeakenFreeSyntax.weakened p.w p.z p.b p.B (p.oldCtx 3) (y 4))
  extraType : Derives Γ (FormulaCodeSyntax.formulaCode p.w (y 0) p.z p.B)
  layout : Derives Γ (ForcingProofContext.layoutData p.w p.z p.B (y 0) (p.Pre 1)
    (ForcingMemberRows.leafFields p.row) (fun i => y i.succ))
  zero : Derives Γ (SyntaxNumeralSyntax.numeral 0 p.z)
  one : Derives Γ (SyntaxNumeralSyntax.numeral 1 p.A1)
  two : Derives Γ (SyntaxNumeralSyntax.numeral 2 p.A2)
  three : Derives Γ (SyntaxNumeralSyntax.numeral 3 p.A3)
  free : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) p.f)
  condition : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) p.j)
  carrier : Derives Γ (SyntaxNumeralSyntax.numeral k p.K)
  row : Derives Γ (ForcingMemberRows.rowData test Reln p.w p.z p.A1 p.A2 p.A3 p.f p.B (p.C 1) (p.v 8)
    (p.v 9) (p.Refl 1) (p.Pre 1) (p.U0 1) p.raw (p.P 1) p.row)

private theorem ModalLive.read {k m} {Γ : Context m} (p : ModalRunArgs m) (test : Formula 1)
    (Reln : Source.Formula (k+2)) (y : Fin 7 → Fin m) (r g Tp Old New : Fin m)
    (h : Derives Γ (p.live test Reln y r g Tp Old New)) :
    ModalLive Γ p test Reln y r g Tp Old New := by
  have hg := Derives.conjL h
  have globalInput := Derives.conjL hg
  have relation := Derives.conjL globalInput
  have members := Derives.conjL relation
  have fresh := Derives.conjL (.conjR globalInput)
  have freshInput := Derives.conjL fresh
  have images := Derives.conjL (.conjR (.conjR freshInput))
  have memberInput := Derives.conjL members
  constructor
  · exact .conjL (.conjR h)
  · exact .conjL (.conjR (.conjR h))
  · intro alpha n S Parent hs hq
    exact .conjI (.conjL (.conjL images)) (.conjI (.conjL freshInput) (.conjI hs
      (.conjI (.conjL (.conjR freshInput)) (.conjI (.conjL (.conjR (.conjL images)))
        (.conjI (.conjL (.conjR fresh)) (.conjI (.conjL (.conjR (.conjR fresh))) hq))))))
  · exact .conjR (.conjR (.conjR hg))
  · exact SyntaxWeakenFreeOutput.target_type p.w p.z p.b p.B p.Extra (y 0) (.conjL (.conjR hg))
  · exact .conjL (.conjR (.conjR hg))
  · exact .conjL memberInput
  · exact .conjL (.conjR memberInput)
  · exact .conjL (.conjR (.conjR memberInput))
  · exact .conjR relation
  · exact .conjL (.conjR (.conjR (.conjR (.conjR memberInput))))
  · exact .conjR (.conjR (.conjR h))
  · exact .conjL (.conjR (.conjR (.conjR memberInput)))
  · exact .conjL (.conjR (.conjR members))

private theorem at_two_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (p : ModalRunArgs m) (test : Formula 1) (n : Fin m)
    (consume : ∀ {l} {Δ : Context l} (rho : Fin m → Fin l) (Old New : Fin l),
      ZFContext.Evidence Δ → (∀ {u}, Derives Γ u → Derives Δ (u.rename rho)) →
      Derives Δ (substituted (rho p.w) (rho p.T) (rho p.SOld) (rho p.a) (rho p.f) (rho p.z) (rho p.b) (rho n) Old) →
      Derives Δ (substituted (rho p.w) (rho p.T) (rho p.SNew) (rho p.a) (rho p.f) (rho p.z) (rho p.b) (rho n) New) →
      Derives Δ (InternalProofBackground.implication test (rho p.w) (rho p.z) (rho p.b) (rho (p.oldCtx 3)) Old) →
      Derives Δ (InternalProofBackground.implication test (rho p.w) (rho p.z) (rho p.b) (rho (p.oldCtx 3)) New)) :
    Derives Γ (ForcingConjunctionMono.transfer test p.w p.z p.a p.f p.b (p.oldCtx 3)
      (fun _ => p.T) (SyntaxAtomSyntax.two p.SOld p.SNew) n) := by
  apply OriginalUniversalBlock.intro_many 2
  apply Derives.impI
  apply Derives.impI
  let rho := old (m := m) 2
  let Q := (substituted (rho p.w) (rho p.T) (rho p.SOld) (rho p.a) (rho p.f) (rho p.z) (rho p.b) (rho n) (slot 2 0)).conj
    (substituted (rho p.w) (rho p.T) (rho p.SNew) (rho p.a) (rho p.f) (rho p.z) (rho p.b) (rho n) (slot 2 1))
  let H := InternalProofBackground.implication test (rho p.w) (rho p.z) (rho p.b) (rho (p.oldCtx 3)) (slot 2 0)
  let Δ := Context.add H (Context.add Q (raisedContext 2 Γ))
  have hQ : Derives Δ Q := .hyp (Or.inr (Or.inl rfl))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact consume rho (slot 2 0) (slot 2 1) (ZFContext.add (HornBinderRules.zf_body 2 hZ Q) H)
    (fun u => SourceLogic.add (HornBinderRules.under_body 2 u Q) H) (.conjL hQ) (.conjR hQ) hH


set_option maxHeartbeats 1800000 in
theorem transfer_negative_global {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha N n : Fin m)
    (hi : Derives Γ ((globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx).conj
        ((successor alpha a).conj
        ((FormulaCodeSyntax.formulaCode w N a f).conj
        (ForcingNegCode.compiled Reln w a alpha f j N n))))) :
    Derives Γ (ForcingConjunctionMono.transfer test w z a f b (oldCtx 3)
      (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n) := by
  let p : ModalRunArgs m := ⟨w, z, a, f, j, b, B, R, S, T, SOld, SNew, A1, A2, A3, K, Extra, raw, v, C, Refl, Pre, U0, P, x, oldCtx⟩
  have runtime : Derives Γ (p.input test Reln) := .conjL hi
  have rest := Derives.conjR hi
  have salpha := Derives.conjL rest
  have rest := Derives.conjR rest
  have child := Derives.conjL rest
  have full := Derives.conjR rest
  apply with_global_runtime hZ test Reln p runtime
  intro l Δ rho y r g Tp Old New zf move live
  let q := p.map rho
  apply of_eq (by simp only [ForcingConjunctionMono.transfer_rename, SyntaxAtomSyntax.two_map]; rfl)
  apply at_two_queries zf q test (rho n)
  intro t Ξ sigma ParentOld ParentNew zf' move' hOld hNew proofOld
  let e := q.map sigma
  let yy := fun i : Fin 7 => sigma (y i)
  let vv := ForcingWeakenedImages.withBound e.v (sigma r) (sigma g) (sigma Tp)
  let rr := fun i => sigma (rho i)
  have raise {u : Formula m} (hu : Derives Γ u) : Derives Ξ (u.rename rr) :=
    of_eq (rename_comp u rho sigma) (move' (move hu))
  have live' := of_eq (ModalRunArgs.live_rename q test Reln y r g Tp Old New sigma) (move' live)
  have h := ModalLive.read e test Reln yy (sigma r) (sigma g) (sigma Tp) (sigma Old) (sigma New) live'
  have salpha := of_eq (successor_rename alpha a rr) (raise salpha)
  have child' := of_eq (FormulaCodeSyntax.formulaCode_rename w N a f rr) (raise child)
  have full' := of_eq (ForcingNegCode.compiled_rename Reln w a alpha f j N n rr) (raise full)
  have sourceOld := h.source (rr alpha) (rr n) e.SOld ParentOld salpha hOld
  have sourceNew := h.source (rr alpha) (rr n) e.SNew ParentNew salpha hNew
  let H := ForcingMemberRows.leafFields e.row
  let Gb := ForcingMemberRows.backgroundFields e.row
  let U := ForcingMemberRows.nativeFields (e.U0 1) e.row
  let F := ForcingMemberRows.proofFields e.row
  let N0 := ForcingMemberRows.tailFields e.row
  let D := ForcingMemberRows.prefixFields e.row
  let ctx := fun i : Fin 6 => yy i.succ

  let params : NegativeArgs t := ⟨e.w, e.z, e.a, e.f, rr alpha, e.b, e.C 1, e.B, e.T, e.S, e.j, rr N, rr n, ParentOld,
    ParentNew, e.A1, e.A2, e.A3, e.C 1, e.v 8, e.Refl 1, e.Pre 1, e.K, e.oldCtx 3, yy 0, e.P 0 2, e.P 0 1,
    e.SOld, e.SNew, sigma Old, sigma New, vv, e.raw, Gb, H, U, F, e.P 1, N0, D, ctx⟩
  apply negative_from_input zf' test Reln params
  refine .conjI h.oldFrame (.conjI h.newFrame (.conjI sourceOld (.conjI sourceNew (.conjI full' ?_))))
  refine .conjI child' (.conjI h.weak (.conjI proofOld (.conjI h.extraType (.conjI h.layout ?_))))
  exact .conjI h.zero (.conjI h.one (.conjI h.two (.conjI h.three (.conjI h.free (.conjI h.carrier h.row)))))

theorem transfer_negative_global_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha N n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence
        (((globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx).conj
        ((successor alpha a).conj
        ((FormulaCodeSyntax.formulaCode w N a f).conj
        (ForcingNegCode.compiled Reln w a alpha f j N n)))).imp
          (ForcingConjunctionMono.transfer test w z a f b (oldCtx 3)
      (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact transfer_negative_global (ZFContext.add (ZFContext.source_ZF m) _) test Reln w z a f j b B R S T SOld SNew A1 A2 A3
      K Extra raw v C Refl Pre U0 P x oldCtx alpha N n (.hyp (Or.inl rfl))

set_option maxHeartbeats 1800000 in
theorem transfer_existential_global {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha beta gamma N n : Fin m)
    (hi : Derives Γ ((globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx).conj
        ((successor alpha a).conj
        ((successor beta alpha).conj
        ((successor gamma beta).conj
        ((FormulaCodeSyntax.formulaCode w N alpha f).conj
        (ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n))))))) :
    Derives Γ (ForcingConjunctionMono.transfer test w z a f b (oldCtx 3)
      (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n) := by
  let p : ModalRunArgs m := ⟨w, z, a, f, j, b, B, R, S, T, SOld, SNew, A1, A2, A3, K, Extra, raw, v, C, Refl, Pre, U0, P, x, oldCtx⟩
  have runtime : Derives Γ (p.input test Reln) := .conjL hi
  have rest := Derives.conjR hi
  have salpha := Derives.conjL rest
  have rest := Derives.conjR rest
  have sbeta := Derives.conjL rest
  have rest := Derives.conjR rest
  have sgamma := Derives.conjL rest
  have rest := Derives.conjR rest
  have child := Derives.conjL rest
  have full := Derives.conjR rest
  apply with_global_runtime hZ test Reln p runtime
  intro l Δ rho y r g Tp Old New zf move live
  let q := p.map rho
  apply of_eq (by simp only [ForcingConjunctionMono.transfer_rename, SyntaxAtomSyntax.two_map]; rfl)
  apply at_two_queries zf q test (rho n)
  intro t Ξ sigma ParentOld ParentNew zf' move' hOld hNew proofOld
  let e := q.map sigma
  let yy := fun i : Fin 7 => sigma (y i)
  let vv := ForcingWeakenedImages.withBound e.v (sigma r) (sigma g) (sigma Tp)
  let rr := fun i => sigma (rho i)
  have raise {u : Formula m} (hu : Derives Γ u) : Derives Ξ (u.rename rr) :=
    of_eq (rename_comp u rho sigma) (move' (move hu))
  have live' := of_eq (ModalRunArgs.live_rename q test Reln y r g Tp Old New sigma) (move' live)
  have h := ModalLive.read e test Reln yy (sigma r) (sigma g) (sigma Tp) (sigma Old) (sigma New) live'
  have salpha := of_eq (successor_rename alpha a rr) (raise salpha)
  have sbeta := of_eq (successor_rename beta alpha rr) (raise sbeta)
  have sgamma := of_eq (successor_rename gamma beta rr) (raise sgamma)
  have child' := of_eq (FormulaCodeSyntax.formulaCode_rename w N alpha f rr) (raise child)
  have full' := of_eq (ForcingExistCode.compiled_rename Reln Dom w a alpha beta gamma f j N n rr) (raise full)
  have sourceOld := h.source (rr alpha) (rr n) e.SOld ParentOld salpha hOld
  have sourceNew := h.source (rr alpha) (rr n) e.SNew ParentNew salpha hNew
  let H := ForcingMemberRows.leafFields e.row
  let Gb := ForcingMemberRows.backgroundFields e.row
  let U := ForcingMemberRows.nativeFields (e.U0 1) e.row
  let F := ForcingMemberRows.proofFields e.row
  let N0 := ForcingMemberRows.tailFields e.row
  let D := ForcingMemberRows.prefixFields e.row
  let ctx := fun i : Fin 6 => yy i.succ

  have oldTable := Derives.conjL (.conjR (.conjR h.oldFrame))
  have newTable := Derives.conjL (.conjR (.conjR h.newFrame))
  apply transfer_existential_compiled zf' test Reln Dom e.w e.z e.a e.f (rr alpha) (rr beta) (rr gamma) e.b (e.C 1)
    e.B e.T e.S e.j (rr N) (rr n) ParentOld ParentNew e.A1 e.A2 e.A3 (e.C 1) (e.v 8) (e.Refl 1) (e.Pre 1)
    e.K (e.oldCtx 3) (yy 0) (e.P 0 2) (e.P 0 1) e.SOld e.SNew (sigma Old) (sigma New)
    vv e.raw Gb H U F (e.P 1) N0 D ctx
  refine .conjI h.oldFrame (.conjI h.newFrame (.conjI sourceOld (.conjI sourceNew (.conjI full' ?_))))
  refine .conjI sbeta (.conjI sgamma (.conjI child' (.conjI h.weak (.conjI proofOld (.conjI h.extraType (.conjI h.layout ?_))))))
  exact .conjI h.zero (.conjI h.one (.conjI h.two (.conjI h.three (.conjI h.free (.conjI h.condition
    (.conjI h.carrier (.conjI h.row (.conjI oldTable newTable))))))))

theorem transfer_existential_global_kernel_certificate {k m} (test : Formula 1) (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m)
    (alpha beta gamma N n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence
        (((globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx).conj
        ((successor alpha a).conj
        ((successor beta alpha).conj
        ((successor gamma beta).conj
        ((FormulaCodeSyntax.formulaCode w N alpha f).conj
        (ForcingExistCode.compiled Reln Dom w a alpha beta gamma f j N n)))))).imp
          (ForcingConjunctionMono.transfer test w z a f b (oldCtx 3)
      (fun _ => T) (SyntaxAtomSyntax.two SOld SNew) n)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact transfer_existential_global (ZFContext.add (ZFContext.source_ZF m) _) test Reln Dom w z a f j b B R S T SOld SNew A1
      A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx alpha beta gamma N n (.hyp (Or.inl rfl))


theorem globalModalInput_rename {k m l} (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z a f j b B R S T SOld SNew A1 A2 A3 K Extra : Fin m)
    (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m) (C Refl Pre U0 : Fin 2 → Fin m)
    (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (rho : Fin m → Fin l) :
    (globalModalInput test Reln w z a f j b B R S T SOld SNew A1 A2 A3 K Extra raw v C Refl Pre U0 P x oldCtx).rename rho =
      globalModalInput test Reln (rho w) (rho z) (rho a) (rho f) (rho j) (rho b) (rho B) (rho R) (rho S) (rho T) (rho SOld)
        (rho SNew) (rho A1) (rho A2) (rho A3) (rho K) (rho Extra) (fun i => rho (raw i)) (fun i => rho (v i))
        (fun i => rho (C i)) (fun i => rho (Refl i)) (fun i => rho (Pre i)) (fun i => rho (U0 i)) (fun s i => rho (P s i))
        (fun i => rho (x i)) (fun i => rho (oldCtx i)) := by
  simp only [globalModalInput, ModalRunArgs.input, ModalRunArgs.aux, Formula.rename,
    ForcingGlobalWeakening.input_rename, SyntaxMixedImageCodeSyntax.termList_rename,
    SyntaxNumeralSyntax.numeral_rename, ForcingReflexiveImages.replacement_rename]

end PPAC.Migration.ForcingRawModalBody

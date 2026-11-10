import PPAC.Migration.ForcingExistTailOpening
import PPAC.Migration.ForcingExistMemberOpening
import PPAC.Migration.ForcingExistOrderOpening
import PPAC.Migration.ForcingExistDomainOpening

/-! Consume ALL FOUR completed actual component comparisons at the SAME
original existential-tail records, then package THREE AND and BOTH EX by
original constructor uniqueness. Runtime scopes/codes are internal.
This record consumer still requires common-head/canonical operation frames;
their production and arbitrary-trace normalization are separate obligations.
No expected leaf/tail equality or guard truth is an assumption. -/
namespace PPAC.Migration.ForcingExistTailComparison
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Repack the existing sixteen actual values: eight outputs and eight
scope/lift coordinates. This constructs metadata only, no object code. -/
def values {m} (B c K H C d L M : Fin m) (v : Fin 8 → Fin m) : Fin 16 → Fin m :=
  (Fin.cases (v 0) (Fin.cases B (Fin.cases c (Fin.cases K (Fin.cases H (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases C (Fin.cases d (Fin.cases L (Fin.cases M (Fin.cases (v 6) (Fin.cases (v 7) Fin.elim0))))))))))))))))

private theorem values_map {m l} (B c K H C d L M : Fin m) (v : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (values B c K H C d L M v i)) =
      values (ρ B) (ρ c) (ρ K) (ρ H) (ρ C) (ρ d) (ρ L) (ρ M) (fun i => ρ (v i)) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.elim0 i) i) i) i) i) i) i) i) i) i) i) i) i) i) i) i) i

def trace {m} (w D S A f z T Y Base j p B c K H C d L M : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m) : Formula m :=
  ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s (values B c K H C d L M v)

theorem trace_rename {m l} (w D S A f z T Y Base j p B c K H C d L M : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (trace w D S A f z T Y Base j p B c K H C d L M s v).rename ρ =
      trace (ρ w) (ρ D) (ρ S) (ρ A) (ρ f) (ρ z) (ρ T) (ρ Y) (ρ Base) (ρ j) (ρ p)
        (ρ B) (ρ c) (ρ K) (ρ H) (ρ C) (ρ d) (ρ L) (ρ M) (fun i => ρ (s i)) (fun i => ρ (v i)) := by
  simp only [trace, ForcingExistTailOpening.scopeData_rename, values_map]

def frame {m} (w z a A B C f T c d R S D Q K H L M E V W head j Base p Y : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m) : Formula m :=
  (ForcingExistChildOpening.frame w z a A B C f T c d R S D Q K H L M E V W head j).conj (trace w D S A f z T Y Base j p B c K H C d L M s v)

theorem frame_rename {m l} (w z a A B C f T c d R S D Q K H L M E V W head j Base p Y : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v).rename ρ =
      frame (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ T) (ρ c) (ρ d) (ρ R) (ρ S) (ρ D) (ρ Q) (ρ K) (ρ H) (ρ L) (ρ M) (ρ E) (ρ V) (ρ W) (ρ head) (ρ j) (ρ Base) (ρ p) (ρ Y) (fun i => ρ (s i)) (fun i => ρ (v i)) := by
  simp only [frame, Formula.rename, ForcingExistChildOpening.frame_rename, trace_rename]

private theorem member_frame {k m} {Γ : Context m} (w z a A B C f T c d R S D Q K H L M E V W head j Base p Y I x : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x)) :
    Derives Γ (ForcingExistMemberOpening.frame k w z A f T B c D S K H Base j p I x) := by
  have hC := Derives.conjL hf
  have hT := Derives.conjR hf
  have hData := Derives.conjL hT
  have hInput := (Derives.conjL (Derives.conjR hT))
  have hBase := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hT))))))
  exact Derives.conjI (Derives.conjL hC) (Derives.conjI (Derives.conjL (Derives.conjR hC)) (Derives.conjI (Derives.conjL hInput)
    (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL hData))) (Derives.conjI (Derives.conjR hBase) (Derives.conjI hi (Derives.conjI hj hx))))))

private theorem order_frame {m} {Γ : Context m} (w z a A B C f T c d R S D Q K H L M E V W head j Base p Y : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v)) :
    Derives Γ (ForcingExistOrderOpening.frame w z A f T B c D S K H j head E) := by
  have hC := Derives.conjL hf
  have hT := Derives.conjR hf
  have hData := Derives.conjL hT
  have hInput := (Derives.conjL (Derives.conjR hT))
  have hRoots := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hT))))
  have hHead := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hC))))))))
  have hE := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hC)))))))))
  have hType := ForcingReflexiveImages.target_type w f c T S j head E hE
  exact Derives.conjI (Derives.conjL hC) (Derives.conjI (Derives.conjL (Derives.conjR hC)) (Derives.conjI (Derives.conjL hInput)
    (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL hData))) (Derives.conjI hHead (Derives.conjI hE (Derives.conjI (Derives.conjL hRoots) hType))))))

private theorem domain_frame {k m} {Γ : Context m} (w z a A B C f T c d R S D Q K H L M E V W head j Base p Y I x Name : Fin m) (s : Fin 9 → Fin m) (v : Fin 8 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hff : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hn : Derives Γ (SyntaxMixedImageHead.head w d T z Name)) :
    Derives Γ (ForcingExistDomainOpening.opening k w z A B C f T c d D S K H L M Base I j p x Name) := by
  have hC := Derives.conjL hf
  have hT := Derives.conjR hf
  have hData := Derives.conjL hT
  have hInput := (Derives.conjL (Derives.conjR hT))
  have hBase := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hT))))))
  exact Derives.conjI (Derives.conjL hC) (Derives.conjI (Derives.conjL (Derives.conjR hC)) (Derives.conjI (Derives.conjL hInput)
    (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL hData)))
      (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hData))))))
        (Derives.conjI (Derives.conjR hBase) (Derives.conjI hi (Derives.conjI hj (Derives.conjI hff (Derives.conjI hx (Derives.conjI hn (Derives.conjL hBase)))))))))))

private theorem single_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w x y n r : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (.equal x y))
    (hn : Derives Γ (singleCode 10 w x n)) (hr : Derives Γ (singleCode 10 w y r)) : Derives Γ (.equal n r) := by
  let P := singleCode 10 w.castSucc (Fin.last m) n.castSucc
  have hn' : Derives Γ (singleCode 10 w y n) :=
    of_eq (by simp only [P, Formula.instantiate, singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn))
  exact SyntaxLogicalFields.single_unique hZ 10 w y n r hw hn' hr

private theorem binary_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w x y X Y n r : Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (.equal x X)) (hy : Derives Γ (.equal y Y))
    (hn : Derives Γ (binaryCode 0 w x y n)) (hr : Derives Γ (binaryCode 0 w X Y r)) : Derives Γ (.equal n r) := by
  let P := binaryCode 0 w.castSucc (Fin.last m) y.castSucc n.castSucc
  have hn0 : Derives Γ (binaryCode 0 w X y n) :=
    of_eq (by simp only [P, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P hx (of_eq (by simp only [P, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn))
  let Q := binaryCode 0 w.castSucc X.castSucc (Fin.last m) n.castSucc
  have hn1 : Derives Γ (binaryCode 0 w X Y n) :=
    of_eq (by simp only [Q, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst Q hy (of_eq (by simp only [Q, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn0))
  exact SyntaxLogicalFields.binary_unique hZ 0 w X Y n r hw hn1 hr

/-- ALL FOUR complete original compilers and ACTUAL leaf queries are
consumed. The five parent equalities follow through original constructors.
Common canonical/head frames are explicit OPERATION hypotheses, never answers. -/
theorem compare {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v))
    (hg : Derives Γ (frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 s u))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hff : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hn : Derives Γ (SyntaxMixedImageHead.head w d T z Name))
    (hm : Derives Γ (ForcingGuardCode.compiled false Reln w B f x (s 7)))
    (ho : Derives Γ (ForcingExistGuardsCode.compiled Reln w A B f j (s 8)))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N (s 6))) :
    Derives Γ (.equal Y Y1) := by
  have hData := Derives.conjL (Derives.conjR hf)
  have gData := Derives.conjL (Derives.conjR hg)
  have hM := (Derives.conjL (Derives.conjR hData))
  have gM := (Derives.conjL (Derives.conjR gData))
  have hO := (Derives.conjL (Derives.conjR (Derives.conjR hData)))
  have gO := (Derives.conjL (Derives.conjR (Derives.conjR gData)))
  have hD := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hData))))
  have gD := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR gData))))
  have hp := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))))
  have hq := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hg)))))))
  have hw := Derives.conjL (Derives.conjL hf)
  have eM := ForcingExistMemberOpening.compare hZ Reln
    w z A f T B c D S K H Base j p I x (s 7) (v 1) S1 K1 H1 q (s 7) (u 1)
    (member_frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y I x s v hf hi hj hx)
    (member_frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 I x s u hg hi hj hx)
    hm hm (Derives.conjL (Derives.conjR hM)) (Derives.conjL (Derives.conjR gM))
  have eO := ForcingExistOrderOpening.guard_compare hZ Reln
    w z A f T B c D S K H j head E (s 8) (v 3) Base p q S1 K1 H1 E1 (s 8) (u 3)
    (order_frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v hf) (order_frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 s u hg)
    ho ho (Derives.conjL (Derives.conjR hO)) (Derives.conjL (Derives.conjR gO)) hp hq
  have eD := ForcingExistDomainOpening.compare hZ Dom
    w z A B C f T c d D S K H L M Base I j p x Name (s 5) (v 6) S1 K1 H1 L1 M1 q (s 5) (u 6)
    (domain_frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y I x Name s v hf hi hj hff hx hn)
    (domain_frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 I x Name s u hg hi hj hff hx hn)
    hd hd (Derives.conjL (Derives.conjR hD)) (Derives.conjL (Derives.conjR gD))
  have eC := ForcingExistChildOpening.compare hZ
    w z a A B C f T c d R S D Q K H L M E V W head j N (s 6) (v 7) Base p q S1 K1 H1 L1 M1 E1 V1 W1 (s 6) (u 7)
    (Derives.conjL hf) (Derives.conjL hg) hc hc
    (Derives.conjR (Derives.conjR hD)) (Derives.conjR (Derives.conjR gD)) hp hq
  have eBody := binary_equal hZ w (v 6) (v 7) (u 6) (u 7) (v 5) (u 5) hw eD eC (Derives.conjL hD) (Derives.conjL gD)
  have eName := single_equal hZ w (v 5) (u 5) (v 4) (u 4) hw eBody
    (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hData))))) (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR gData)))))
  have eRest := binary_equal hZ w (v 3) (v 4) (u 3) (u 4) (v 2) (u 2) hw eO eName (Derives.conjL hO) (Derives.conjL gO)
  have eInner := binary_equal hZ w (v 1) (v 2) (u 1) (u 2) (v 0) (u 0) hw eM eRest (Derives.conjL hM) (Derives.conjL gM)
  exact single_equal hZ w (v 0) (u 0) Y Y1 hw eInner
    (Derives.conjL (Derives.conjL hData)) (Derives.conjL (Derives.conjL gData))

def input {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) : Formula m :=
  (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v).conj ((frame w z a A B C f T c d R S1 D Q K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 s u).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxVariableSyntax.code true w z x).conj ((SyntaxMixedImageHead.head w d T z Name).conj ((ForcingGuardCode.compiled false Reln w B f x (s 7)).conj ((ForcingExistGuardsCode.compiled Reln w A B f j (s 8)).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)).conj ((ForcingExistChildCode.compiled w a A B C f j N (s 6))))))))))))

theorem input_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (input Reln Dom w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 s v u).rename ρ =
      input Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ T) (ρ c) (ρ d) (ρ R) (ρ D) (ρ Q) (ρ Base) (ρ I) (ρ j) (ρ p) (ρ q) (ρ x) (ρ head) (ρ Name) (ρ N) (ρ S) (ρ K) (ρ H) (ρ L) (ρ M) (ρ E) (ρ V) (ρ W) (ρ Y) (ρ S1) (ρ K1) (ρ H1) (ρ L1) (ρ M1) (ρ E1) (ρ V1) (ρ W1) (ρ Y1) (fun i => ρ (s i)) (fun i => ρ (v i)) (fun i => ρ (u i)) := by
  simp only [input, Formula.rename, frame_rename, SyntaxNumeralSyntax.numeral_rename,
    SyntaxVariableSyntax.code_rename, SyntaxMixedImageHead.head_rename,
    ForcingGuardCode.compiled_rename, ForcingExistGuardsCode.compiled_rename, ForcingExistChildCode.compiled_rename]

def sentence {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) : Source.Sentence :=
  ((input Reln Dom w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 s v u).imp (.equal Y Y1)).close

theorem kernel_certificate {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence Reln Dom w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 s v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input Reln Dom w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 s v u
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact compare (ZFContext.add (ZFContext.source_ZF m) G) Reln Dom w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 K1 H1 L1 M1 E1 V1 W1 Y1 s v u
    (Derives.conjL hG)
    (Derives.conjL (Derives.conjR hG))
    (Derives.conjL (Derives.conjR (Derives.conjR hG)))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hG))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG)))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG))))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hG))))))))))

end PPAC.Migration.ForcingExistTailComparison

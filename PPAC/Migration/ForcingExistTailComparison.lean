import PPAC.Migration.ForcingExistTailOpening
import PPAC.Migration.ForcingExistMemberOpening
import PPAC.Migration.ForcingExistOrderOpening
import PPAC.Migration.ForcingExistDomainOpening
import PPAC.Migration.NativeProofQuotation

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

private theorem compare_name {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x head Name N S K H L M E V W Y S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hf : Derives Γ (frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y s v))
    (hg : Derives Γ (frame w z a A B C f T c d R S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 s u))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hff : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hn : Derives Γ (SyntaxMixedImageHead.head w d T z Name))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N (s 6))) :
    Derives Γ (.equal (v 4) (u 4)) := by
  have hData := Derives.conjL (Derives.conjR hf)
  have gData := Derives.conjL (Derives.conjR hg)
  have hD := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hData))))
  have gD := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR gData))))
  have hp := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))))
  have hq := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hg)))))))
  have hw := Derives.conjL (Derives.conjL hf)
  have eD := ForcingExistDomainOpening.compare_prefixes hZ Dom
    w z A B C f T c d D S K H L M Base I j p x Name (s 5) (v 6) D1 S1 K1 H1 L1 M1 q (s 5) (u 6)
    (domain_frame w z a A B C f T c d R S D Q K H L M E V W head j Base p Y I x Name s v hf hi hj hff hx hn)
    (domain_frame w z a A B C f T c d R S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 head j Base q Y1 I x Name s u hg hi hj hff hx hn)
    hd hd (Derives.conjL (Derives.conjR hD)) (Derives.conjL (Derives.conjR gD))
  have eC := ForcingExistChildOpening.compare_prefixes hZ
    w z a A B C f T c d R S D Q K H L M E V W head j N (s 6) (v 7) Base p q S1 D1 Q1 K1 H1 L1 M1 E1 V1 W1 (s 6) (u 7)
    (Derives.conjL hf) (Derives.conjL hg) hc hc
    (Derives.conjR (Derives.conjR hD)) (Derives.conjR (Derives.conjR gD)) hp hq
  have eBody := binary_equal hZ w (v 6) (v 7) (u 6) (u 7) (v 5) (u 5) hw eD eC (Derives.conjL hD) (Derives.conjL gD)
  exact single_equal hZ w (v 5) (u 5) (v 4) (u 4) hw eBody
    (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hData))))) (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR gData)))))

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
  have eName := compare_name hZ Dom w z a A B C f T c d R D Q Base I j p q x head Name N
    S K H L M E V W Y S1 D Q K1 H1 L1 M1 E1 V1 W1 Y1 s v u hf hg hi hj hff hx hn hd hc
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

/-- Promote the original closed old-name list by the EXISTING free-list
graph witness and free/mixed graph bridge. Its code is unchanged. -/
private theorem closed_names_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a z c T R : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (.mem c w))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z T R)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w a c T R) := by
  have hFree := EmptyBoundFreeInputs.list_free hZ w a z T R hw hz hR
  let E := SyntaxFreeSubstSyntax.listBody w a T R
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hFree
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hGraph := EmptyBoundFreeInputs.graph_mixed w.castSucc (Fin.last m) a.castSucc c.castSucc T.castSucc
    (under hc E) (Derives.conjR hE)
  have hType := SyntaxMixedImageCodeFields.term_list w.castSucc (Fin.last m) a.castSucc c.castSucc T.castSucc R.castSucc
    (Derives.conjI hGraph (Derives.conjL hE))
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w a c T R Fin.castSucc).symm hType

/-- Only ORIGINAL closed root layout, arbitrary internal child typing,
actual normalized traces and complete original compiler records. No common
head, canonical overwrite/lift/query, leaf equality or final answer supplied. -/
def initialInput {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A a).conj ((SyntaxMixedImageCodeSyntax.termList w a z T R).conj ((SyntaxTermSyntax.term w z T Q).conj ((StructuralListSyntax.consCode w Q R D).conj ((FormulaCodeSyntax.formulaCode w N A f).conj ((trace w D S A f z T Y Base j p B c K H C d L M s v).conj ((trace w D S1 A f z T Y1 Base j q B c K1 H1 C d L1 M1 s u).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxVariableSyntax.code true w z x).conj ((ForcingGuardCode.compiled false Reln w B f x (s 7)).conj ((ForcingExistGuardsCode.compiled Reln w A B f j (s 8)).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)).conj ((ForcingExistChildCode.compiled w a A B C f j N (s 6))))))))))))))))))

theorem initialInput_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u).rename ρ =
      initialInput Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ T) (ρ c) (ρ d) (ρ R) (ρ D) (ρ Q) (ρ Base) (ρ I) (ρ j) (ρ p) (ρ q) (ρ x) (ρ N) (ρ S) (ρ K) (ρ H) (ρ L) (ρ M) (ρ Y) (ρ S1) (ρ K1) (ρ H1) (ρ L1) (ρ M1) (ρ Y1) (fun i => ρ (s i)) (fun i => ρ (v i)) (fun i => ρ (u i)) := by
  simp only [initialInput, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxMixedImageCodeSyntax.termList_rename, SyntaxTermSyntax.term_rename, StructuralListSyntax.consCode_rename,
    FormulaCodeSyntax.formulaCode_rename, trace_rename, SyntaxNumeralSyntax.numeral_rename,
    SyntaxVariableSyntax.code_rename, ForcingGuardCode.compiled_rename,
    ForcingExistGuardsCode.compiled_rename, ForcingExistChildCode.compiled_rename]

private theorem canonical_from_traces {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a A B C f T c d R D D1 Base j p q N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (hNames : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z T R))
    (hN : Derives Γ (FormulaCodeSyntax.formulaCode w N A f))
    (hTrace : Derives Γ (trace w D S A f z T Y Base j p B c K H C d L M s v))
    (gTrace : Derives Γ (trace w D1 S1 A f z T Y1 Base j q B c K1 H1 C d L1 M1 s u)) :
    Derives Γ (ForcingExistChildCanonical.result w z a A c d f T R S S1 j N) := by
  have hFirst := (Derives.conjL (Derives.conjR hTrace))
  have hSecond := (Derives.conjL (Derives.conjR (Derives.conjR hTrace)))
  have hRoots := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hTrace))))
  have hBase := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hTrace))))))
  have gBase := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR gTrace))))))
  have hzNat := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjL (Derives.conjL hFirst))))
  have hcNat := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjL hRoots)))
  have hR := closed_names_scope hZ w a z c T R hw hz hcNat hNames
  have hCan : Derives Γ (ForcingExistChildCanonical.input w z z c d a A f T R Base p q S S1 j N) :=
    Derives.conjI hw (Derives.conjI hz (Derives.conjI hzNat
      (Derives.conjI (Derives.conjR (Derives.conjR hFirst))
        (Derives.conjI (Derives.conjR (Derives.conjR hSecond))
          (Derives.conjI hA (Derives.conjI (Derives.conjI hR (Derives.conjL hBase))
            (Derives.conjI (Derives.conjR hBase) (Derives.conjI (Derives.conjR gBase) hN))))))))
  exact ForcingExistChildCanonical.derive hZ w z z c d a A f T R Base p q S S1 j N hCan

private theorem canonical_from_initial {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hi : Derives Γ (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u)) :
    Derives Γ (ForcingExistChildCanonical.result w z a A c d f T R S S1 j N) := by
  have hw := (Derives.conjL hi)
  have hz := (Derives.conjL (Derives.conjR hi))
  have hTrace := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))
  have gTrace := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))
  exact canonical_from_traces hZ w z a A B C f T c d R D D Base j p q N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u
    hw hz (.conjL (.conjR (.conjR hi))) (.conjL (.conjR (.conjR (.conjR hi))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))) hTrace gTrace

private def canonicalBody {m} (w a A c d f T R S j head N : Fin m) : Formula (m+4) :=
  ForcingExistChildCanonical.oneData (old 4 w) (old 4 a) (old 4 A) (old 4 c) (old 4 d) (old 4 f) (old 4 T)
    (old 4 R) (old 4 S) (old 4 j) (old 4 head) (old 4 N) (slot 4)
private def canonicalResult {m} (w a A c d f T R S j head N : Fin m) : Formula m :=
  existsMany 4 (canonicalBody w a A c d f T R S j head N)

/-- The SAME canonical overwrite and lift generated once are used by the
child frame; the existing compare derives its order frame from that SAME E. -/
private theorem frame_from_generated {m} {Γ : Context m}
    (w z a A B C f T c d R D Q Base j p N S K H L M Y head : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 8 → Fin m) (l : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z T R))
    (hQ : Derives Γ (SyntaxTermSyntax.term w z T Q))
    (hCons : Derives Γ (StructuralListSyntax.consCode w Q R D))
    (ht : Derives Γ (trace w D S A f z T Y Base j p B c K H C d L M s v))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w c T z head))
    (hl : Derives Γ (ForcingExistChildCanonical.oneData w a A c d f T R S j head N l)) :
    Derives Γ (frame w z a A B C f T c d R S D Q K H L M (l 0) (l 1) (l 2) head j Base p Y s v) := by
  have hData := Derives.conjL ht
  have hFirst := (Derives.conjL (Derives.conjR ht))
  have hSourceS := Derives.conjR (Derives.conjL hFirst)
  have hChild : Derives Γ (ForcingExistChildOpening.frame w z a A B C f T c d R S D Q K H L M (l 0) (l 1) (l 2) head j) :=
    Derives.conjI hw (Derives.conjI hz (Derives.conjI (Derives.conjI hR hSourceS)
      (Derives.conjI hQ (Derives.conjI hCons
        (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL hData)))
          (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hData))))))
            (Derives.conjI hHead (Derives.conjI (Derives.conjL hl) (Derives.conjL (Derives.conjR hl))))))))))
  exact Derives.conjI hChild ht

private theorem head_after_second_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z A B C f T c d D S Y Base j p K H L M head : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 8 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (trace w D S A f z T Y Base j p B c K H C d L M s v))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w c T z head)) :
    Derives Γ (SyntaxMixedImageHead.head w d T z head) := by
  have hRoots := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR ht))))
  have hSecond := (Derives.conjL (Derives.conjR (Derives.conjR ht)))
  have hcNat := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjL hRoots)))
  have hTNat := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjL hRoots)))
  have hCode := Derives.conjL (Derives.conjR hHead)
  exact
    Derives.conjI hz (Derives.conjI hCode
      (SyntaxMixedImageHead.term_at_zero hZ w c d T z head hw hcNat hTNat
        (Derives.conjR (Derives.conjR hSecond)) hz hCode))

private theorem at_generated {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 head : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) (l r : Fin 4 → Fin m)
    (hi : Derives Γ (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w c T z head))
    (hl : Derives Γ (ForcingExistChildCanonical.oneData w a A c d f T R S j head N l))
    (hr : Derives Γ (ForcingExistChildCanonical.oneData w a A c d f T R S1 j head N r)) :
    Derives Γ (.equal Y Y1) := by
  have hw := (Derives.conjL hi)
  have hz := (Derives.conjL (Derives.conjR hi))
  have hNames := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hi))))
  have hQ := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))
  have hCons := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))
  have ht := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))
  have gt := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))
  have hf := frame_from_generated w z a A B C f T c d R D Q Base j p N S K H L M Y head s v l hw hz hNames hQ hCons ht hHead hl
  have hg := frame_from_generated w z a A B C f T c d R D Q Base j q N S1 K1 H1 L1 M1 Y1 head s u r hw hz hNames hQ hCons gt hHead hr
  have hName := head_after_second_lift hZ w z A B C f T c d D S Y Base j p K H L M head s v hw hz ht hHead
  exact compare hZ Reln Dom w z a A B C f T c d R D Q Base I j p q x head head N
    S K H L M (l 0) (l 1) (l 2) Y S1 K1 H1 L1 M1 (r 0) (r 1) (r 2) Y1 s v u
    hf hg (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))) hName
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))))

private theorem after_left {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 head : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) (l : Fin 4 → Fin m)
    (hi : Derives Γ (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w c T z head))
    (hl : Derives Γ (ForcingExistChildCanonical.oneData w a A c d f T R S j head N l))
    (hr : Derives Γ (canonicalResult w a A c d f T R S1 j head N)) :
    Derives Γ (.equal Y Y1) := by
  let E := canonicalBody w a A c d f T R S1 j head N
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hr
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 := of_eq (initialInput_rename Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u (old 4)) (HornBinderRules.under_body 4 hi E)
  have hh4 := of_eq (SyntaxMixedImageHead.head_rename w c T z head (old 4)) (HornBinderRules.under_body 4 hHead E)
  have hl4 := of_eq (ForcingExistChildCanonical.oneData_rename w a A c d f T R S j head N l (old 4)) (HornBinderRules.under_body 4 hl E)
  exact at_generated (HornBinderRules.zf_body 4 hZ E) Reln Dom (old 4 w) (old 4 z) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 f) (old 4 T) (old 4 c) (old 4 d) (old 4 R) (old 4 D) (old 4 Q) (old 4 Base) (old 4 I) (old 4 j) (old 4 p) (old 4 q) (old 4 x) (old 4 N) (old 4 S) (old 4 K) (old 4 H) (old 4 L) (old 4 M) (old 4 Y) (old 4 S1) (old 4 K1) (old 4 H1) (old 4 L1) (old 4 M1) (old 4 Y1) (old 4 head)
    (fun i => old 4 (s i)) (fun i => old 4 (v i)) (fun i => old 4 (u i)) (fun i => old 4 (l i)) (slot 4) hi4 hh4 hl4 hE

private theorem after_head {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 head : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hi : Derives Γ (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u))
    (hd : Derives Γ (ForcingExistChildCanonical.data w z a A c d f T R S S1 j N head)) :
    Derives Γ (.equal Y Y1) := by
  have hl : Derives Γ (canonicalResult w a A c d f T R S j head N) := Derives.conjL (Derives.conjR hd)
  let E := canonicalBody w a A c d f T R S j head N
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hl
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi4 := of_eq (initialInput_rename Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u (old 4)) (HornBinderRules.under_body 4 hi E)
  have hd4 := of_eq (ForcingExistChildCanonical.data_rename w z a A c d f T R S S1 j N head (old 4)) (HornBinderRules.under_body 4 hd E)
  have hr4 : Derives Δ (canonicalResult (old 4 w) (old 4 a) (old 4 A) (old 4 c) (old 4 d) (old 4 f) (old 4 T)
      (old 4 R) (old 4 S1) (old 4 j) (old 4 head) (old 4 N)) := Derives.conjL (Derives.conjR (Derives.conjR hd4))
  exact after_left (HornBinderRules.zf_body 4 hZ E) Reln Dom (old 4 w) (old 4 z) (old 4 a) (old 4 A) (old 4 B) (old 4 C) (old 4 f) (old 4 T) (old 4 c) (old 4 d) (old 4 R) (old 4 D) (old 4 Q) (old 4 Base) (old 4 I) (old 4 j) (old 4 p) (old 4 q) (old 4 x) (old 4 N) (old 4 S) (old 4 K) (old 4 H) (old 4 L) (old 4 M) (old 4 Y) (old 4 S1) (old 4 K1) (old 4 H1) (old 4 L1) (old 4 M1) (old 4 Y1) (old 4 head)
    (fun i => old 4 (s i)) (fun i => old 4 (v i)) (fun i => old 4 (u i)) (slot 4) hi4 (Derives.conjL hd4) hE hr4

/-- Produce and erase ALL NINE existing canonical witnesses internally.
The SAME generated head serves both actual target scopes via term_at_zero;
the SAME two overwrites/lifts feed the completed whole-tail comparison.
NO common head or canonical operation record remains a premise. -/
theorem from_initial {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hi : Derives Γ (initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u)) : Derives Γ (.equal Y Y1) := by
  have hc := canonical_from_initial hZ Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u hi
  let E := ForcingExistChildCanonical.data w.castSucc z.castSucc a.castSucc A.castSucc c.castSucc d.castSucc f.castSucc T.castSucc
    R.castSucc S.castSucc S1.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi1 := of_eq (initialInput_rename Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u Fin.castSucc) (under hi E)
  exact after_head (ZFContext.under hZ E) Reln Dom w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc T.castSucc c.castSucc d.castSucc R.castSucc D.castSucc Q.castSucc Base.castSucc I.castSucc j.castSucc p.castSucc q.castSucc x.castSucc N.castSucc S.castSucc K.castSucc H.castSucc L.castSucc M.castSucc Y.castSucc S1.castSucc K1.castSucc H1.castSucc L1.castSucc M1.castSucc Y1.castSucc (Fin.last m)
    (fun i => (s i).castSucc) (fun i => (v i).castSucc) (fun i => (u i).castSucc) hi1 hE


/-- The name existential is independent of the two outer conditions.
Use the original tail traces, with their actual and possibly different prefixes.
The inner head and both canonical child computations are derived in ZF. -/
private theorem name_from_traces {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q D1 Q1 Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A a))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z T R))
    (hQ : Derives Γ (SyntaxTermSyntax.term w z T Q))
    (hQ1 : Derives Γ (SyntaxTermSyntax.term w z T Q1))
    (hCons : Derives Γ (StructuralListSyntax.consCode w Q R D))
    (hCons1 : Derives Γ (StructuralListSyntax.consCode w Q1 R D1))
    (hN : Derives Γ (FormulaCodeSyntax.formulaCode w N A f))
    (ht : Derives Γ (trace w D S A f z T Y Base j p B c K H C d L M s v))
    (gt : Derives Γ (trace w D1 S1 A f z T Y1 Base j q B c K1 H1 C d L1 M1 s u))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N (s 6))) :
    Derives Γ (.equal (v 4) (u 4)) := by
  have hex := canonical_from_traces hZ w z a A B C f T c d R D D1 Base j p q N S K H L M Y S1 K1 H1 L1 M1 Y1
    s v u hw hz hA hR hN ht gt
  let out : Formula m := .equal (v 4) (u 4)
  refine NativeProofQuotation.eliminate_objects hZ 1 (fun r h =>
    ForcingExistChildCanonical.data (r w) (r z) (r a) (r A) (r c) (r d) (r f) (r T) (r R) (r S) (r S1) (r j) (r N) (h 0))
    hex out ?_
  intro m1 Γ1 r h hZ1 lift hData
  refine NativeProofQuotation.eliminate_objects hZ1 4 (fun t l =>
    ForcingExistChildCanonical.oneData (t (r w)) (t (r a)) (t (r A)) (t (r c)) (t (r d)) (t (r f)) (t (r T))
      (t (r R)) (t (r S)) (t (r j)) (t (h 0)) (t (r N)) l)
    (.conjL (.conjR hData)) (out.rename r) ?_
  intro m2 Γ2 t l hZ2 move hLeft
  have hBoth := of_eq (ForcingExistChildCanonical.data_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ t) (move hData)
  refine NativeProofQuotation.eliminate_objects hZ2 4 (fun e u =>
    ForcingExistChildCanonical.oneData (e (t (r w))) (e (t (r a))) (e (t (r A))) (e (t (r c))) (e (t (r d))) (e (t (r f))) (e (t (r T)))
      (e (t (r R))) (e (t (r S1))) (e (t (r j))) (e (t (h 0))) (e (t (r N))) u)
    (.conjL (.conjR (.conjR hBoth))) ((out.rename r).rename t) ?_
  intro m3 Γ3 e right hZ3 extend hRight
  let g := e ∘ t ∘ r
  let head := e (t (h 0))
  have transport {F : Formula m} (p0 : Derives Γ F) : Derives Γ3 (F.rename g) :=
    of_eq (SourceAlgebra.rename_comp F r (e ∘ t))
      (of_eq (SourceAlgebra.rename_comp (F.rename r) t e) (extend (move (lift p0))))
  have hw3 := of_eq (omega_rename _ g) (transport hw)
  have hz3 := of_eq (empty_rename _ g) (transport hz)
  have hR3 := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ g) (transport hR)
  have hHead3 := of_eq (SyntaxMixedImageHead.head_rename _ _ _ _ _ e) (extend (.conjL hBoth))
  have hLeft3 := of_eq (ForcingExistChildCanonical.oneData_rename _ _ _ _ _ _ _ _ _ _ _ _ l e) (extend hLeft)
  have ht3 := of_eq (trace_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s v g) (transport ht)
  have gt3 := of_eq (trace_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s u g) (transport gt)
  have hF := frame_from_generated (g w) (g z) (g a) (g A) (g B) (g C) (g f) (g T) (g c) (g d) (g R)
    (g D) (g Q) (g Base) (g j) (g p) (g N) (g S) (g K) (g H) (g L) (g M) (g Y) head
    (g ∘ s) (g ∘ v) (e ∘ l) hw3 hz3 hR3
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ g) (transport hQ))
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ g) (transport hCons)) ht3 hHead3 hLeft3
  have gF := frame_from_generated (g w) (g z) (g a) (g A) (g B) (g C) (g f) (g T) (g c) (g d) (g R)
    (g D1) (g Q1) (g Base) (g j) (g q) (g N) (g S1) (g K1) (g H1) (g L1) (g M1) (g Y1) head
    (g ∘ s) (g ∘ u) right hw3 hz3 hR3
    (of_eq (SyntaxTermSyntax.term_rename _ _ _ _ g) (transport hQ1))
    (of_eq (StructuralListSyntax.consCode_rename _ _ _ _ g) (transport hCons1)) gt3 hHead3 hRight
  have hName := head_after_second_lift hZ3 (g w) (g z) (g A) (g B) (g C) (g f) (g T) (g c) (g d)
    (g D) (g S) (g Y) (g Base) (g j) (g p) (g K) (g H) (g L) (g M) head (g ∘ s) (g ∘ v) hw3 hz3 ht3 hHead3
  exact compare_name hZ3 Dom (g w) (g z) (g a) (g A) (g B) (g C) (g f) (g T) (g c) (g d) (g R) (g D) (g Q)
    (g Base) (g I) (g j) (g p) (g q) (g x) head head (g N) (g S) (g K) (g H) (g L) (g M) (e (l 0)) (e (l 1)) (e (l 2))
    (g Y) (g S1) (g D1) (g Q1) (g K1) (g H1) (g L1) (g M1) (right 0) (right 1) (right 2) (g Y1)
    (g ∘ s) (g ∘ v) (g ∘ u) hF gF
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (transport hi))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (transport hj))
    (of_eq (SyntaxNumeralSyntax.numeral_rename _ _ g) (transport hf))
    (of_eq (SyntaxVariableSyntax.code_rename _ _ _ _ g) (transport hx)) hName
    (of_eq (ForcingGuardCode.compiled_rename _ _ _ _ _ _ _ g) (transport hd))
    (of_eq (ForcingExistChildCode.compiled_rename _ _ _ _ _ _ _ _ _ g) (transport hc))

def initialSentence {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) : Source.Sentence :=
  ((initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u).imp (.equal Y Y1)).close

theorem initial_kernel_certificate {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 8 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (initialSentence Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := initialInput Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact from_initial (ZFContext.add (ZFContext.source_ZF m) G) Reln Dom w z a A B C f T c d R D Q Base I j p q x N S K H L M Y S1 K1 H1 L1 M1 Y1 s v u hG

/-- Existing sixteen actual coordinates, repacked without producing codes. -/
private def observed {m} (v : Fin 16 → Fin m) : Fin 8 → Fin m :=
  Fin.cases (v 0) (Fin.cases (v 5) (Fin.cases (v 6) (Fin.cases (v 7)
    (Fin.cases (v 8) (Fin.cases (v 9) (Fin.cases (v 14) (Fin.cases (v 15) Fin.elim0)))))))

private theorem actual_trace {m} {Γ : Context m} (w D S A f z T Y Base j p : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 16 → Fin m)
    (hv : Derives Γ (ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s v)) :
    Derives Γ (trace w D S A f z T Y Base j p (v 1) (v 2) (v 3) (v 4)
      (v 10) (v 11) (v 12) (v 13) s (observed v)) := hv

/-- Substitute only the FOUR scope coordinates using actual object equalities.
The actual map tables, output codes and full query records are retained. -/
private theorem trace_scopes {m} {Γ : Context m}
    (w D S A f z T Y Base j p B c K H C d L M B1 c1 C1 d1 : Fin m)
    (s : Fin 9 → Fin m) (v : Fin 8 → Fin m)
    (hB : Derives Γ (.equal B B1)) (hc : Derives Γ (.equal c c1))
    (hC : Derives Γ (.equal C C1)) (hd : Derives Γ (.equal d d1))
    (ht : Derives Γ (trace w D S A f z T Y Base j p B c K H C d L M s v)) :
    Derives Γ (trace w D S A f z T Y Base j p B1 c1 K H C1 d1 L M s v) := by
  let P0 := trace w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc Y.castSucc Base.castSucc j.castSucc p.castSucc (Fin.last m) c.castSucc K.castSucc H.castSucc C.castSucc d.castSucc L.castSucc M.castSucc (fun i => (s i).castSucc) (fun i => (v i).castSucc)
  have ht0 : Derives Γ (trace w D S A f z T Y Base j p B1 c K H C d L M s v) :=
    of_eq (by simp only [P0, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P0 hB
        (of_eq (by simp only [P0, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht))
  let P1 := trace w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc Y.castSucc Base.castSucc j.castSucc p.castSucc B1.castSucc (Fin.last m) K.castSucc H.castSucc C.castSucc d.castSucc L.castSucc M.castSucc (fun i => (s i).castSucc) (fun i => (v i).castSucc)
  have ht1 : Derives Γ (trace w D S A f z T Y Base j p B1 c1 K H C d L M s v) :=
    of_eq (by simp only [P1, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P1 hc
        (of_eq (by simp only [P1, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht0))
  let P2 := trace w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc Y.castSucc Base.castSucc j.castSucc p.castSucc B1.castSucc c1.castSucc K.castSucc H.castSucc (Fin.last m) d.castSucc L.castSucc M.castSucc (fun i => (s i).castSucc) (fun i => (v i).castSucc)
  have ht2 : Derives Γ (trace w D S A f z T Y Base j p B1 c1 K H C1 d L M s v) :=
    of_eq (by simp only [P2, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P2 hC
        (of_eq (by simp only [P2, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht1))
  let P3 := trace w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc Y.castSucc Base.castSucc j.castSucc p.castSucc B1.castSucc c1.castSucc K.castSucc H.castSucc C1.castSucc (Fin.last m) L.castSucc M.castSucc (fun i => (s i).castSucc) (fun i => (v i).castSucc)
  have ht3 : Derives Γ (trace w D S A f z T Y Base j p B1 c1 K H C1 d1 L M s v) :=
    of_eq (by simp only [P3, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P3 hd
        (of_eq (by simp only [P3, Formula.instantiate, trace_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ht2))
  exact ht3

/-- Literal closed-opening ROOT input and TWO ACTUAL raw-tail queries.
All source compilers remain exact; no trace, output, scope equality, common
head or canonical operation witness is supplied. -/
def rawInput {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A a).conj ((successor B A).conj ((successor C B).conj ((SyntaxMixedImageCodeSyntax.termList w a z T R).conj ((SyntaxTermSyntax.term w z T Q).conj ((StructuralListSyntax.consCode w Q R D).conj ((FormulaCodeSyntax.formulaCode w N A f).conj ((ForcingReflexiveImages.replacement w f z T Base j p S).conj ((ForcingReflexiveImages.replacement w f z T Base j q S1).conj ((ForcingExistTailOpening.source w s).conj ((Internal.SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T (s 0) Y).conj ((Internal.SyntaxMixedFormulaJudgmentSyntax.substituted w D S1 A f z T (s 0) Y1).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxVariableSyntax.code true w z x).conj ((ForcingGuardCode.compiled false Reln w B f x (s 7)).conj ((ForcingExistGuardsCode.compiled Reln w A B f j (s 8)).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)).conj ((ForcingExistChildCode.compiled w a A B C f j N (s 6)))))))))))))))))))))))

theorem rawInput_rename {k m l} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) (ρ : Fin m → Fin l) :
    (rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s).rename ρ =
      rawInput Reln Dom (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ C) (ρ f) (ρ T) (ρ R) (ρ D) (ρ Q) (ρ Base) (ρ I) (ρ j) (ρ p) (ρ q) (ρ x) (ρ N) (ρ S) (ρ Y) (ρ S1) (ρ Y1) (fun i => ρ (s i)) := by
  simp only [rawInput, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxMixedImageCodeSyntax.termList_rename, SyntaxTermSyntax.term_rename, StructuralListSyntax.consCode_rename,
    FormulaCodeSyntax.formulaCode_rename, ForcingReflexiveImages.replacement_rename,
    ForcingExistTailOpening.source_rename, Internal.SyntaxMixedFormulaJudgmentSyntax.substituted_rename,
    SyntaxNumeralSyntax.numeral_rename, SyntaxVariableSyntax.code_rename,
    ForcingGuardCode.compiled_rename, ForcingExistGuardsCode.compiled_rename, ForcingExistChildCode.compiled_rename]

private theorem normalized_traces {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w A B C f z T D S Y D1 S1 Y1 Base j p q : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 16 → Fin m)
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hv : Derives Γ (ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s v))
    (hu : Derives Γ (ForcingExistTailOpening.scopeData w D1 S1 A f z T Y1 Base j q s u)) :
    Derives Γ ((trace w D S A f z T Y Base j p B (v 2) (v 3) (v 4) C (v 11) (v 12) (v 13) s (observed v)).conj
      (trace w D1 S1 A f z T Y1 Base j q B (v 2) (u 3) (u 4) C (v 11) (u 12) (u 13) s (observed u))) := by
  have hFirst := (Derives.conjL (Derives.conjR hv))
  have hSecond := (Derives.conjL (Derives.conjR (Derives.conjR hv)))
  have hExt := (ZFContext.arithmetic hZ).base.extensionality
  have eB := OmegaUniversal.successor_unique (v 1) B A hExt
    (Derives.conjL (Derives.conjR hFirst)) hB
  let P := successor (v 10).castSucc (Fin.last m)
  have hPred : Derives Γ (successor (v 10) B) :=
    of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P eB
        (of_eq (by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
          (Derives.conjL (Derives.conjR hSecond))))
  have eC := OmegaUniversal.successor_unique (v 10) C B hExt hPred hC
  have hAlign := ForcingExistTailOpening.scope_alignment_at_prefixes hZ w D S D1 S1 A f z T Y Y1 Base j p q s v u hv hu
  refine .conjI ?_ ?_
  · exact trace_scopes w D S A f z T Y Base j p (v 1) (v 2) (v 3) (v 4) (v 10) (v 11) (v 12) (v 13)
      B (v 2) C (v 11) s (observed v) eB (Derives.eqRefl (v 2)) eC (Derives.eqRefl (v 11))
      (actual_trace w D S A f z T Y Base j p s v hv)
  · exact trace_scopes w D1 S1 A f z T Y1 Base j q (u 1) (u 2) (u 3) (u 4) (u 10) (u 11) (u 12) (u 13)
      B (v 2) C (v 11) s (observed u)
      (eq_trans (eq_symm (Derives.conjL hAlign)) eB)
      (eq_symm (Derives.conjL (Derives.conjR hAlign)))
      (eq_trans (eq_symm (Derives.conjL (Derives.conjR (Derives.conjR hAlign)))) eC)
      (eq_symm (Derives.conjR (Derives.conjR (Derives.conjR hAlign))))
      (actual_trace w D1 S1 A f z T Y1 Base j q s u hu)


/-- Compare the name fields of two actual openings while the inner condition
is still bound. The outer-condition prefixes and selected updates can differ. -/
theorem name_from_opened_tails {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q D1 Q1 Base I j p q x N S Y S1 Y1 : Fin m)
    (s : Fin 9 → Fin m) (v u : Fin 16 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hR : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z T R))
    (hQ : Derives Γ (SyntaxTermSyntax.term w z T Q))
    (hQ1 : Derives Γ (SyntaxTermSyntax.term w z T Q1))
    (hCons : Derives Γ (StructuralListSyntax.consCode w Q R D))
    (hCons1 : Derives Γ (StructuralListSyntax.consCode w Q1 R D1))
    (hN : Derives Γ (FormulaCodeSyntax.formulaCode w N A f))
    (hv : Derives Γ (ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s v))
    (hu : Derives Γ (ForcingExistTailOpening.scopeData w D1 S1 A f z T Y1 Base j q s u))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hj : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w C f x (s 5)))
    (hc : Derives Γ (ForcingExistChildCode.compiled w a A B C f j N (s 6))) :
    Derives Γ (.equal (v 8) (u 8)) := by
  have h := normalized_traces hZ w A B C f z T D S Y D1 S1 Y1 Base j p q s v u hB hC hv hu
  exact name_from_traces hZ Dom w z a A B C f T (v 2) (v 11) R D Q D1 Q1 Base I j p q x N
    S (v 3) (v 4) (v 12) (v 13) Y S1 (u 3) (u 4) (u 12) (u 13) Y1 s (observed v) (observed u)
    hw hz hA hR hQ hQ1 hCons hCons1 hN (.conjL h) (.conjR h) hi hj hf hx hd hc

private theorem at_raw_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) (v u : Fin 16 → Fin m)
    (hi : Derives Γ (rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s))
    (hv : Derives Γ (ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s v))
    (hu : Derives Γ (ForcingExistTailOpening.scopeData w D S1 A f z T Y1 Base j q s u)) :
    Derives Γ (.equal Y Y1) := by
  have hTraces := normalized_traces hZ w A B C f z T D S Y D S1 Y1 Base j p q s v u
    (.conjL (.conjR (.conjR (.conjR hi)))) (.conjL (.conjR (.conjR (.conjR (.conjR hi))))) hv hu
  have ht := Derives.conjL hTraces
  have gt := Derives.conjR hTraces
  have hInitial : Derives Γ (initialInput Reln Dom
    w z a A B C f T (v 2) (v 11) R D Q Base I j p q x N S (v 3) (v 4) (v 12) (v 13) Y
    S1 (u 3) (u 4) (u 12) (u 13) Y1 s (observed v) (observed u)) :=
    Derives.conjI (Derives.conjL hi) (Derives.conjI (Derives.conjL (Derives.conjR hi)) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR hi))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))) (Derives.conjI ht (Derives.conjI gt (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))))))))) ((Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))))))))))))))))))))))))))
  exact from_initial hZ Reln Dom w z a A B C f T (v 2) (v 11) R D Q Base I j p q x N
    S (v 3) (v 4) (v 12) (v 13) Y S1 (u 3) (u 4) (u 12) (u 13) Y1 s (observed v) (observed u) hInitial

private theorem after_first_raw {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) (v : Fin 16 → Fin m)
    (hi : Derives Γ (rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s))
    (hv : Derives Γ (ForcingExistTailOpening.scopeData w D S A f z T Y Base j p s v)) :
    Derives Γ (.equal Y Y1) := by
  have hu := ForcingExistTailOpening.prepare_query hZ w D S1 A f z T Y1 Base j q s
    (Derives.conjL hi) (Derives.conjL (Derives.conjR hi)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))))))))))))
  let E := ForcingExistTailOpening.scopeBody w D S1 A f z T Y1 Base j q s
  let Δ := Context.add E (raisedContext 16 Γ)
  apply HornBinderRules.eliminate_many 16 E _ hu
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi16 := of_eq (rawInput_rename Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s (old 16)) (HornBinderRules.under_body 16 hi E)
  have hv16 := of_eq (ForcingExistTailOpening.scopeData_rename w D S A f z T Y Base j p s v (old 16))
    (HornBinderRules.under_body 16 hv E)
  exact at_raw_records (HornBinderRules.zf_body 16 hZ E) Reln Dom (old 16 w) (old 16 z) (old 16 a) (old 16 A) (old 16 B) (old 16 C) (old 16 f) (old 16 T) (old 16 R) (old 16 D) (old 16 Q) (old 16 Base) (old 16 I) (old 16 j) (old 16 p) (old 16 q) (old 16 x) (old 16 N) (old 16 S) (old 16 Y) (old 16 S1) (old 16 Y1)
    (fun i => old 16 (s i)) (fun i => old 16 (v i)) (slot 16) hi16 hv16 hE

/-- Whole ORIGINAL raw existential-tail condition independence. BOTH complete
actual trace families and ALL common canonical operations are internally
produced/eliminated. No supplied trace/head/canonical table/scope equality,
leaf equality or tail-output equality; all source/target/code data internal. -/
theorem from_queries {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m)
    (hi : Derives Γ (rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s)) : Derives Γ (.equal Y Y1) := by
  have hv := ForcingExistTailOpening.prepare_query hZ w D S A f z T Y Base j p s
    (Derives.conjL hi) (Derives.conjL (Derives.conjR hi)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))))))))))
  let E := ForcingExistTailOpening.scopeBody w D S A f z T Y Base j p s
  let Δ := Context.add E (raisedContext 16 Γ)
  apply HornBinderRules.eliminate_many 16 E _ hv
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi16 := of_eq (rawInput_rename Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s (old 16)) (HornBinderRules.under_body 16 hi E)
  exact after_first_raw (HornBinderRules.zf_body 16 hZ E) Reln Dom (old 16 w) (old 16 z) (old 16 a) (old 16 A) (old 16 B) (old 16 C) (old 16 f) (old 16 T) (old 16 R) (old 16 D) (old 16 Q) (old 16 Base) (old 16 I) (old 16 j) (old 16 p) (old 16 q) (old 16 x) (old 16 N) (old 16 S) (old 16 Y) (old 16 S1) (old 16 Y1)
    (fun i => old 16 (s i)) (slot 16) hi16 hE

def rawSentence {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) : Source.Sentence :=
  ((rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s).imp (.equal Y Y1)).close

theorem raw_kernel_certificate {k m} (Reln : Source.Formula (k+2)) (Dom : Source.Formula (k+1))
    (w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 : Fin m) (s : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (rawSentence Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := rawInput Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact from_queries (ZFContext.add (ZFContext.source_ZF m) G) Reln Dom w z a A B C f T R D Q Base I j p q x N S Y S1 Y1 s hG

end PPAC.Migration.ForcingExistTailComparison

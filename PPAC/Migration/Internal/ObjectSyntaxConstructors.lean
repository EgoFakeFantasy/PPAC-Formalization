import PPAC.Migration.Internal.SyntaxVariables

/-! 原语法数码、精确字段、有限标签及全部内部变量索引构造的原核闭句模式。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxConstructors
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax SyntaxForestSyntax SyntaxNodeSyntax

def numeralExistsSentence {m} (k : Nat) (w : Fin m) : Source.Sentence := ((omega w).imp (SyntaxNumeralSyntax.existsNumeral w k)).close

def numeralUniqueSentence {m} (k : Nat) (x y : Fin m) : Source.Sentence := ((numeral k x).imp ((numeral k y).imp (Formula.equal x y))).close

def numeralRangeSentence {m} (k : Nat) (w x : Fin m) : Source.Sentence := ((omega w).imp ((numeral k x).imp (Formula.mem x w))).close

def numeralLessSentence {m} (i j : Nat) (x y : Fin m) : Source.Sentence := ((numeral i x).imp ((numeral j y).imp (Formula.mem x y))).close

def numeralDifferentSentence {m} (i j : Nat) (x y : Fin m) : Source.Sentence := ((numeral i x).imp ((numeral j y).imp ((Formula.equal x y).neg))).close

def forestExistsSentence {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((inputs k w xs).imp (existsForest k w xs))).close

def forestUniqueSentence {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n s : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((forest k w xs s).imp (Formula.equal n s)))).close

def forestMemberSentence {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp (Formula.mem (xs i) n))).close

def forestLengthSentence {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((numeral k l).imp (StructuralListLengthSyntax.hasLength w n l)))).close

def nodeFiberSentence {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((inputs k w xs).imp (nodeFiber k w tag xs)))).close

def nodeMemberSentence {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((node k w tag xs n).imp (Formula.mem (xs i) n))).close

def constructorFiberSentence {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((inputs k w xs).imp (constructorFiber k tag w xs))).close

def constructorDisjointSentence {m} (k l a b : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) : Source.Sentence := ((omega w).imp ((constructor k a w xs n).imp ((constructor l b w ys n).imp (Formula.bot)))).close

def constructorMemberSentence {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp (Formula.mem (xs i) n))).close

def scalarFiberSentence {m} (w i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp (nodeFiber 0 w i Fin.elim0))).close

def scalarInjectiveSentence {m} (w i j n : Fin m) : Source.Sentence := ((omega w).imp ((scalar w i n).imp ((scalar w j n).imp (Formula.equal i j)))).close

def variableFiberSentence {m} (bound : Bool) (w i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp (SyntaxVariableSyntax.fiber bound w i))).close

def variableDisjointSentence {m} (w i j n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxVariableSyntax.code true w i n).imp ((SyntaxVariableSyntax.code false w j n).imp (Formula.bot)))).close

theorem source_numeralExists {m} (k : Nat) (w : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (numeralExistsSentence k w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNumerals.exists_numeral hZ k w (.hyp (Or.inl rfl))

theorem numeralExists_kernel_certificate {m} (k : Nat) (w : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralExistsSentence k w)) := TheoryTransport.sentence (source_numeralExists k w )

theorem native_numeralExists {m} (k : Nat) (w : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralExistsSentence k w)) := ZFReplay.replay (numeralExists_kernel_certificate k w )

theorem source_numeralUnique {m} (k : Nat) (x y : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (numeralUniqueSentence k x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral k y) (Context.add (numeral k x) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNumerals.unique hZ k x y (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem numeralUnique_kernel_certificate {m} (k : Nat) (x y : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralUniqueSentence k x y)) := TheoryTransport.sentence (source_numeralUnique k x y )

theorem native_numeralUnique {m} (k : Nat) (x y : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralUniqueSentence k x y)) := ZFReplay.replay (numeralUnique_kernel_certificate k x y )

theorem source_numeralRange {m} (k : Nat) (w x : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (numeralRangeSentence k w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral k x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNumerals.range hZ k w x (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem numeralRange_kernel_certificate {m} (k : Nat) (w x : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralRangeSentence k w x)) := TheoryTransport.sentence (source_numeralRange k w x )

theorem native_numeralRange {m} (k : Nat) (w x : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralRangeSentence k w x)) := ZFReplay.replay (numeralRange_kernel_certificate k w x )

theorem source_numeralLess {m} (i j : Nat) (x y : Fin m) (hij : i < j) : Derives (Source.SetLanguage.ZF.at 0) (numeralLessSentence i j x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j y) (Context.add (numeral i x) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNumerals.less hZ i j hij x y (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem numeralLess_kernel_certificate {m} (i j : Nat) (x y : Fin m) (hij : i < j) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralLessSentence i j x y)) := TheoryTransport.sentence (source_numeralLess i j x y hij)

theorem native_numeralLess {m} (i j : Nat) (x y : Fin m) (hij : i < j) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralLessSentence i j x y)) := ZFReplay.replay (numeralLess_kernel_certificate i j x y hij)

theorem source_numeralDifferent {m} (i j : Nat) (x y : Fin m) (hij : i ≠ j) : Derives (Source.SetLanguage.ZF.at 0) (numeralDifferentSentence i j x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j y) (Context.add (numeral i x) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNumerals.different hZ i j hij x y (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem numeralDifferent_kernel_certificate {m} (i j : Nat) (x y : Fin m) (hij : i ≠ j) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralDifferentSentence i j x y)) := TheoryTransport.sentence (source_numeralDifferent i j x y hij)

theorem native_numeralDifferent {m} (i j : Nat) (x y : Fin m) (hij : i ≠ j) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralDifferentSentence i j x y)) := ZFReplay.replay (numeralDifferent_kernel_certificate i j x y hij)

theorem source_forestExists {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (forestExistsSentence k w xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (inputs k w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForests.exists_forest hZ k w xs (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestExists_kernel_certificate {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestExistsSentence k w xs)) := TheoryTransport.sentence (source_forestExists k w xs )

theorem native_forestExists {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestExistsSentence k w xs)) := ZFReplay.replay (forestExists_kernel_certificate k w xs )

theorem source_forestUnique {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n s : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (forestUniqueSentence k w xs n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (forest k w xs s) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForests.unique hZ k w xs n s (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestUnique_kernel_certificate {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n s : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestUniqueSentence k w xs n s)) := TheoryTransport.sentence (source_forestUnique k w xs n s )

theorem native_forestUnique {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n s : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestUniqueSentence k w xs n s)) := ZFReplay.replay (forestUnique_kernel_certificate k w xs n s )

theorem source_forestMember {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (forestMemberSentence k w xs n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForests.entry_member hZ k w xs n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestMember_kernel_certificate {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestMemberSentence k w xs n i)) := TheoryTransport.sentence (source_forestMember k w xs n i )

theorem native_forestMember {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestMemberSentence k w xs n i)) := ZFReplay.replay (forestMember_kernel_certificate k w xs n i )

theorem source_forestLength {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (forestLengthSentence k w xs n l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral k l) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForestLength.at_numeral hZ k w xs n l (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestLength_kernel_certificate {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestLengthSentence k w xs n l)) := TheoryTransport.sentence (source_forestLength k w xs n l )

theorem native_forestLength {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestLengthSentence k w xs n l)) := ZFReplay.replay (forestLength_kernel_certificate k w xs n l )

theorem source_nodeFiber {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (nodeFiberSentence k w tag xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (inputs k w xs) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodes.exists_unique hZ k w tag xs (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nodeFiber_kernel_certificate {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeFiberSentence k w tag xs)) := TheoryTransport.sentence (source_nodeFiber k w tag xs )

theorem native_nodeFiber {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeFiberSentence k w tag xs)) := ZFReplay.replay (nodeFiber_kernel_certificate k w tag xs )

theorem source_nodeMember {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (nodeMemberSentence k w tag xs n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (node k w tag xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodes.child_member hZ k w tag xs n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nodeMember_kernel_certificate {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeMemberSentence k w tag xs n i)) := TheoryTransport.sentence (source_nodeMember k w tag xs n i )

theorem native_nodeMember {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeMemberSentence k w tag xs n i)) := ZFReplay.replay (nodeMember_kernel_certificate k w tag xs n i )

theorem source_constructorFiber {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (constructorFiberSentence k tag w xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (inputs k w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxConstructors.exists_unique hZ k tag w xs (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem constructorFiber_kernel_certificate {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorFiberSentence k tag w xs)) := TheoryTransport.sentence (source_constructorFiber k tag w xs )

theorem native_constructorFiber {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorFiberSentence k tag w xs)) := ZFReplay.replay (constructorFiber_kernel_certificate k tag w xs )

theorem source_constructorDisjoint {m} (k l a b : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hab : a ≠ b) : Derives (Source.SetLanguage.ZF.at 0) (constructorDisjointSentence k l a b w xs ys n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor l b w ys n) (Context.add (constructor k a w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxConstructors.disjoint hZ k l a b hab w xs ys n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem constructorDisjoint_kernel_certificate {m} (k l a b : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hab : a ≠ b) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorDisjointSentence k l a b w xs ys n)) := TheoryTransport.sentence (source_constructorDisjoint k l a b w xs ys n hab)

theorem native_constructorDisjoint {m} (k l a b : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hab : a ≠ b) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorDisjointSentence k l a b w xs ys n)) := ZFReplay.replay (constructorDisjoint_kernel_certificate k l a b w xs ys n hab)

theorem source_constructorMember {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (constructorMemberSentence k tag w xs n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxConstructors.child_member hZ k tag w xs n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem constructorMember_kernel_certificate {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorMemberSentence k tag w xs n i)) := TheoryTransport.sentence (source_constructorMember k tag w xs n i )

theorem native_constructorMember {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorMemberSentence k tag w xs n i)) := ZFReplay.replay (constructorMember_kernel_certificate k tag w xs n i )

theorem source_scalarFiber {m} (w i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (scalarFiberSentence w i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodes.exists_unique hZ 0 w i Fin.elim0 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)) (.eqRefl w)

theorem scalarFiber_kernel_certificate {m} (w i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scalarFiberSentence w i)) := TheoryTransport.sentence (source_scalarFiber w i )

theorem native_scalarFiber {m} (w i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scalarFiberSentence w i)) := ZFReplay.replay (scalarFiber_kernel_certificate w i )

theorem source_scalarInjective {m} (w i j n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (scalarInjectiveSentence w i j n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (scalar w j n) (Context.add (scalar w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodes.tags_equal hZ 0 0 w i j Fin.elim0 Fin.elim0 n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem scalarInjective_kernel_certificate {m} (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scalarInjectiveSentence w i j n)) := TheoryTransport.sentence (source_scalarInjective w i j n )

theorem native_scalarInjective {m} (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scalarInjectiveSentence w i j n)) := ZFReplay.replay (scalarInjective_kernel_certificate w i j n )

theorem source_variableFiber {m} (bound : Bool) (w i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (variableFiberSentence bound w i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxVariables.exists_unique hZ bound w i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem variableFiber_kernel_certificate {m} (bound : Bool) (w i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableFiberSentence bound w i)) := TheoryTransport.sentence (source_variableFiber bound w i )

theorem native_variableFiber {m} (bound : Bool) (w i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableFiberSentence bound w i)) := ZFReplay.replay (variableFiber_kernel_certificate bound w i )

theorem source_variableDisjoint {m} (w i j n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (variableDisjointSentence w i j n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j n) (Context.add (SyntaxVariableSyntax.code true w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxVariables.disjoint hZ w i j n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem variableDisjoint_kernel_certificate {m} (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableDisjointSentence w i j n)) := TheoryTransport.sentence (source_variableDisjoint w i j n )

theorem native_variableDisjoint {m} (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableDisjointSentence w i j n)) := ZFReplay.replay (variableDisjoint_kernel_certificate w i j n )

end PPAC.Migration.Internal.ObjectSyntaxConstructors

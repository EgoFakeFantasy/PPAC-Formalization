import PPAC

/-! 反向句法的对象核回放；不宣称Replacement/Collection或两种AC已等价。 -/
namespace PPAC.Migration.Step3Checks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev noAxioms : FirstOrder.Theory ℒ := fun _ => False

def binders : FirstOrder.Sentence ℒ :=
  .forallE .set (.existsE .set (.neg
    (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))))

/-- 原生首变量绑定严格变成源末变量绑定。 -/
example : Reverse.sentence binders = .all (.ex ((Source.Formula.mem 0 1).neg)) := rfl

/-- 原生独立连接词展开成源8构造器，无真值谓词或新符号。 -/
example : Reverse.sentence (.iff .truth (.neg .falsum)) =
    (Source.Formula.imp .bot .bot).iff (.imp .bot .bot) := rfl

/-- 嵌套混合量词的等价是实际对象推导，而不是Realize定理。 -/
theorem binder_roundtrip : FirstOrder.Derives noAxioms []
    (.iff binders (Translation.sentence (Reverse.sentence binders))) :=
  Reverse.sentence_equivalent binders

def allConnectives : FirstOrder.Sentence ℒ :=
  .conj (.iff .truth (.imp .falsum .falsum))
    (.forallE .set (.disj (.equal (.bvar .here) (.bvar .here))
      (.existsE .set (.neg (.equal (.bvar .here) (.bvar (.there .here)))))))

theorem all_connectives_roundtrip : FirstOrder.Derives noAxioms []
    (.iff allConnectives (Translation.sentence (Reverse.sentence allConnectives))) :=
  Reverse.sentence_equivalent allConnectives

example : Reverse.sentence (Translation.sentence Source.SetLanguage.PP) = Source.SetLanguage.PP :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.AC) = Source.SetLanguage.AC :=
  Reverse.source_sentence_roundtrip _
example : Reverse.sentence (Translation.sentence Source.SetLanguage.ACwo) = Source.SetLanguage.ACwo :=
  Reverse.source_sentence_roundtrip _

/-- 任意参数个数和任意矩阵，非有限样本。 -/
theorem replacement_roundtrip {n} (p : Source.Formula (n+2)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.replacement p)) =
      Source.SetLanguage.replacement p := Reverse.source_sentence_roundtrip _

theorem separation_roundtrip {n} (p : Source.Formula (n+1)) :
    Reverse.sentence (Translation.sentence (Source.SetLanguage.separation p)) =
      Source.SetLanguage.separation p := Reverse.source_sentence_roundtrip _

/-- 任意理论和开放推导均可在规范化公理呈现间回放。 -/
theorem presentation_replay {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (h : FirstOrder.Derives T Γ p) :
    FirstOrder.Derives (Presentation.theory T) Γ p := Presentation.derives_iff.mpr h

theorem native_ZF_presentation {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free} :
    FirstOrder.Derives (Presentation.theory nativeZF) Γ p ↔
      FirstOrder.Derives nativeZF Γ p := Presentation.derives_iff

/-- 原生外延公理的规范化确实落在source语法像；不等同于源ZF呈现等价。 -/
theorem native_extensionality_replay :
    FirstOrder.Derives (Presentation.theory nativeZF) []
      (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := by
  apply Presentation.replay_original_axiom
  exact ⟨_, SetTheory.ZF.Axiom.extensionality, rfl⟩

/-- 五条已对齐公理，验收源→原生、原生→源句子像两个方向。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.extensionality) :=
  ZFEquivalence.source_extensionality
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.emptySet) :=
  ZFEquivalence.source_emptySet
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.pairing) :=
  ZFEquivalence.source_pairing
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.union) :=
  ZFEquivalence.source_union
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.powerSet) :=
  ZFEquivalence.source_powerSet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.extensionality) := ZFEquivalence.native_extensionality
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.emptySet) := ZFEquivalence.native_emptySet
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.pairing) := ZFEquivalence.native_pairing
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.union) := ZFEquivalence.native_union
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.powerSet) := ZFEquivalence.native_powerSet
/-- 七条固定公理已经双向覆盖；新增两条均为对象原核推导。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.infinity) := ZFEquivalence.source_infinity
example : FirstOrder.Derives nativeZF [] (Translation.sentence Source.SetLanguage.foundation) := ZFEquivalence.source_foundation
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.infinity) := ZFEquivalence.native_infinity
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence SetTheory.Axioms.foundation) := ZFEquivalence.native_foundation

/-- 全分离模式，不限制参数个数和矩阵复杂度。 -/
theorem separation_source_to_native {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.separation p)) :=
  SeparationSyntax.source_separation p

theorem separation_native_of_source_matrix {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence
        (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p))) :=
  SeparationSyntax.native_separation_of_source_matrix p

/-- 多个参数和内嵌混合量词的实例也走同一个全模式定理。 -/
def parameterMatrix : Source.Formula 4 :=
  .all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 4 3).imp (.equal 1 2))))
example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.separation parameterMatrix)) :=
  SeparationSyntax.source_separation parameterMatrix
/-- 任意原生矩阵的反向分离模式，不再只限于ProjectSyntax.unary p。 -/
theorem arbitrary_native_separation {n} (s : SetTheory.Definitional.Project.UnarySchema n) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation s)) :=
  SeparationReverse.native_separation s

def projectMatrix : SetTheory.Definitional.Project.UnarySchema 2 where
  body := .iff .truth (.forallE (.imp
    (SetTheory.Definitional.Project.Formula.subset (.bound 0) (.bound 1))
    (.neg (SetTheory.Definitional.Project.Formula.extensionalEq (.bound 2) (.bound 3)))))
  freeClosed := by simp [SetTheory.Definitional.Formula.FreeClosed]

/-- 子集原子、独立连接词、多个参数和量词同时出现的实际原核回放。 -/
example : FirstOrder.Derives ZFEquivalence.sourceZF []
    (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.separation projectMatrix)) :=
  SeparationReverse.native_separation projectMatrix

/-- 全参数Collection的源呈现只从原Collection版ZF取得，没有假定源ZF已经证明它。 -/
theorem collection_source_presentation {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (CollectionSyntax.collection p)) :=
  CollectionSyntax.source_collection p

theorem arbitrary_collection_roundtrip {n} (s : SetTheory.Definitional.Project.BinarySchema n) :
    FirstOrder.Derives noAxioms [] (.iff
      (SetTheory.Definitional.Project.fo_sentence (SetTheory.Axioms.Schema.collection s))
      (Translation.sentence (CollectionSyntax.collection (ProjectDecode.reverse s.body s.freeClosed)))) :=
  CollectionSyntax.native_collection_equivalent s
/-- 任意参数及任意矩阵的原始Replacement句子，实际在原Collection版ZF内推导。 -/
theorem all_source_replacement {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.native_replacement p

/-- 两模式实例的原核证书与原ZF回放分开验收，防止循环假定Replacement。 -/
theorem replacement_two_instances {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives (TheoryTransport.theory (ReplacementFromCollection.assumptions p)) []
      (Translation.sentence (Source.SetLanguage.replacement p)) :=
  ReplacementFromCollection.kernel_certificate p

theorem source_ZF_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.ZF.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence p) := ZFReplay.source_closed_at h

theorem source_target_full_replay {n} {p : Source.Sentence}
    (h : Source.Derives (Source.SetLanguage.targetTheory.at n) (p.rename Fin.elim0)) :
    FirstOrder.Derives targetTheory [] (Translation.sentence p) := ZFReplay.source_target_closed_at h

/-- 实际源Replacement公理证书经完整源ZF接口回放；不再停留在未对应的理论像。 -/
theorem replay_replacement_through_source_ZF {n} (p : Source.Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.replacement p)) := by
  apply ZFReplay.source_closed_at (n := 1)
  exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement p, rfl⟩

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement (Source.Formula.equal 0 1 : Source.Formula 2))) :=
  ReplacementFromCollection.native_replacement _

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (Source.SetLanguage.replacement
      (Source.Formula.all (.ex ((Source.Formula.mem 5 0).conj ((Source.Formula.mem 3 4).imp (.equal 1 2)))) : Source.Formula 4))) :=
  ReplacementFromCollection.native_replacement _
/-- 六规则总接口，包括任意开放结论、局部假设和非单射变量编号。 -/
theorem native_open_reverse {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Γ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (d : FirstOrder.Derives T Γ p) {n} (default : Fin n) (f : Reverse.Vars free n) :
    Source.Derives (ReverseCompile.context T f Γ) (Reverse.formula ReverseSubstitution.empty f p) :=
  ReverseCompile.derives d default f

theorem every_native_logical_mode {free : Syntax.Ctx} {p : Syntax.Fm [] free}
    (h : HilbertBaseAxiom ℒ p) {n} {Γ : Source.Context n} (f : Reverse.Vars free n) :
    Source.Derives Γ (Reverse.formula ReverseSubstitution.empty f p) :=
  ReverseLogicalAxioms.replay h f

/-- 无函数常元的纯语言：存在对象由原核强化规则证明，回译不能假定Fin 0有变量。 -/
def inhabited : FirstOrder.Sentence ℒ := .existsE .set (.equal (.bvar .here) (.bvar .here))

def inhabitedCertificate : HilbertDerivation noAxioms [] inhabited := by
  apply HilbertDerivation.free_strengthening (sort := SetSort.set)
  change HilbertDerivation noAxioms [SetSort.set]
    (.existsE SetSort.set (.equal (.bvar .here) (.bvar .here)))
  exact .modus_ponens (.logical_axiom (.equality_reflexivity (.fvar .here)))
    (.logical_axiom (.exists_introduction (σ := ℒ) (free := [SetSort.set]) SetSort.set (.equal (.bvar .here) (.bvar .here)) (.fvar .here)))

example : Source.Derives ((Presentation.source noAxioms).at 1)
    ((Reverse.sentence inhabited).rename Fin.elim0) :=
  ReverseCompile.sentence ⟨inhabitedCertificate⟩

/-- 直接在源空理论的一个变量环境证明确切回译句，没有非空公理。 -/
example : Source.Derives (Source.Theory.at (fun _ : Source.Sentence => False) 1)
    ((Reverse.sentence inhabited).rename Fin.elim0) := by
  have h := ReverseCompile.sentence ⟨inhabitedCertificate⟩
  apply Source.Derives.weaken _ h
  rintro q ⟨_, ⟨_, hfalse, _⟩, _⟩
  exact False.elim hfalse

theorem arbitrary_source_sentence_roundtrip {T : Source.Theory} {p : Source.Sentence} :
    FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence p) ↔
      Source.Derives (T.at 1) (p.rename Fin.elim0) :=
  ReverseCompile.source_sentence_iff
/-- 极小元与有界归纳均返回原核Derives，矩阵和参数数目完全任意。 -/
theorem full_bounded_minimal_schema {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedMinimal.sentence p)) :=
  BoundedMinimal.native_minimal p

theorem full_bounded_induction_schema {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedInduction.sentence p)) :=
  BoundedInduction.native_induction p

/-- 源Replacement版ZF端亦有证书，本引理没有使用源Collection。 -/
theorem source_bounded_induction_without_collection {n} (p : Source.Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (BoundedInduction.sentence p) :=
  BoundedInduction.source_ZF_induction p

/-- 一个分离实例与Foundation足够，和原生ZF句子闭合可信基分开验收。 -/
theorem bounded_minimal_two_instances {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (BoundedMinimal.assumptions p)) []
      (Translation.sentence (BoundedMinimal.sentence p)) :=
  BoundedMinimal.kernel_certificate p

theorem bounded_induction_two_instances {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (BoundedMinimal.assumptions p.neg)) []
      (Translation.sentence (BoundedInduction.sentence p)) :=
  BoundedInduction.kernel_certificate p

example : FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedMinimal.sentence parameterMatrix)) :=
  BoundedMinimal.native_minimal parameterMatrix

example : FirstOrder.Derives nativeZF [] (Translation.sentence (BoundedInduction.sentence parameterMatrix)) :=
  BoundedInduction.native_induction parameterMatrix
/-- 全部对象x/y都有唯一Kuratowski编码，输出实际原核闭句。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPairs.existenceSentence) :=
  ObjectPairs.native_exists_unique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPairs.characterizationSentence) :=
  ObjectPairs.native_characterization

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectPairs.existenceSentence :=
  ObjectPairs.source_ZF_exists_unique

example : FirstOrder.Derives (TheoryTransport.theory ObjectPairs.assumptions) []
    (Translation.sentence ObjectPairs.characterizationSentence) := ObjectPairs.characterization_kernel_certificate

/-- 编码严格使用源PP/AC中同一个orderedPair定义。 -/
example {n} (p x y : Fin n) : Source.SetLanguage.orderedPair p x y = PairSyntax.ordered p x y :=
  PairSyntax.ordered_original p x y

/-- 对象x=y也覆盖：同一个变量槽的实际全称闭句，不以分量不同为前提。 -/
def diagonalOrderedPair : Source.Sentence := (ObjectPairs.existsUnique (0 : Fin 1) 0).close

theorem diagonal_ordered_pair : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalOrderedPair) := by
  apply ObjectPairs.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  exact ObjectPairs.exists_unique 0 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)

/-- 任意非单射变量编号及任意局部假设的完整开放分量刻画。 -/
theorem arbitrary_ordered_pair_characterization {n} {Γ : Source.Context n} (p q x y a b : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Source.Derives Γ (PairSyntax.ordered p x y)) (hq : Source.Derives Γ (PairSyntax.ordered q a b)) :
    Source.Derives Γ ((Source.Formula.equal p q).iff ((Source.Formula.equal x a).conj (.equal y b))) :=
  OrderedPairLogic.characterization p q x y a b he hp hq
/-- 源edge/functionOn的完整AST严格保留，未删去无杂项或精确定义域条件。 -/
example {n} (f x y : Fin n) : Source.SetLanguage.edge f x y = GraphSyntax.edge f x y :=
  GraphSyntax.edge_original f x y

example {n} (f d : Fin n) : Source.SetLanguage.functionOn f d = GraphSyntax.functionOn f d :=
  GraphSyntax.functionOn_original f d

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.singletonSentence) := ObjectGraphs.native_singleton
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.evaluationSentence) := ObjectGraphs.native_evaluation
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.domainSentence) := ObjectGraphs.native_domain
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.singleValuedSentence) := ObjectGraphs.native_single_valued

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphs.singletonSentence := ObjectGraphs.source_ZF_singleton
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphs.assumptions) []
    (Translation.sentence ObjectGraphs.singletonSentence) := ObjectGraphs.singleton_kernel_certificate

/-- 开放接口直接证明源原functionOn，包括定义域/图的所有原量词。 -/
theorem singleton_is_original_function {n} {Γ : Source.Context n} (f p d x y : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Source.Derives Γ (PairSyntax.pair f p p)) (hp : Source.Derives Γ (PairSyntax.ordered p x y))
    (hd : Source.Derives Γ (PairSyntax.pair d x x)) : Source.Derives Γ (Source.SetLanguage.functionOn f d) := by
  rw [GraphSyntax.functionOn_original]
  exact SingletonGraphLogic.function_on_singleton f p d x y he hf hp hd

/-- 重复输入/输出槽也走同一原核证书；不存在暗加的不同性前提。 -/
def diagonalSingletonMap : Source.Sentence := (SingletonMap.existsMap (0 : Fin 1) 0).close

theorem diagonal_singleton_map : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalSingletonMap) := by
  apply ObjectPairs.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  exact SingletonMap.exists_map 0 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphs.totalSentence) := ObjectGraphs.native_total
/-- 实际集合插入、原successor、一般新点图扩展及全部边刻画。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.insertSentence) := ObjectGraphInsert.native_insert
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.successorSentence) := ObjectGraphInsert.native_successor
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.extensionSentence) := ObjectGraphInsert.native_extension
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.edgeLawSentence) := ObjectGraphInsert.native_edge_law

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphInsert.extensionSentence := ObjectGraphInsert.source_ZF_extension
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphInsert.assumptions) []
    (Translation.sentence ObjectGraphInsert.extensionSentence) := ObjectGraphInsert.extension_kernel_certificate

example {n} (b a : Fin n) : Source.SetLanguage.successor b a = InsertSyntax.insert b a a := InsertSyntax.successor_original b a

/-- 开放扩展结论仍是完整源functionOn，而不是只保留边的单值性。 -/
theorem extension_is_original_function {n} {Γ : Source.Context n} (g e f d p x y : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Source.Derives Γ (Source.SetLanguage.functionOn f d)) (hn : Source.Derives Γ (Source.Formula.mem x d).neg)
    (hg : Source.Derives Γ (InsertSyntax.insert g f p)) (hd : Source.Derives Γ (InsertSyntax.insert e d x))
    (hp : Source.Derives Γ (PairSyntax.ordered p x y)) : Source.Derives Γ (Source.SetLanguage.functionOn g e) := by
  rw [GraphSyntax.functionOn_original] at hf ⊢
  exact GraphInsertFunction.function_insert g e f d p x y he hf hn hg hd hp

/-- 新点的输出可等于输入；原前提仅为输入不在旧域。 -/
def diagonalGraphExtension : Source.Sentence :=
  ((GraphSyntax.functionOn (0 : Fin 3) 1).imp ((Source.Formula.mem 2 1).neg.imp
    (GraphInsertSyntax.existsExtension 0 1 2 2))).close

theorem diagonal_graph_extension : FirstOrder.Derives nativeZF [] (Translation.sentence diagonalGraphExtension) := by
  apply ObjectGraphInsert.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  apply Source.Derives.impI
  apply Source.Derives.impI
  have hp : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.pairing.rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hu : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.union.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩
  have he : Source.Derives (ObjectGraphInsert.assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩
  exact GraphInsertExistence.exists_extension 0 1 2 2 (SourceLogic.add (SourceLogic.add hp _) _)
    (SourceLogic.add (SourceLogic.add hu _) _) (SourceLogic.add (SourceLogic.add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphInsert.uniquenessSentence) := ObjectGraphInsert.native_uniqueness
/-- 图限制的六个完整原核闭句，覆盖任意对象集合而非有限域。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.setSentence) := ObjectRestriction.native_set
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.functionSentence) := ObjectRestriction.native_function
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.edgeSentence) := ObjectRestriction.native_edge
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.uniqueSentence) := ObjectRestriction.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.identitySentence) := ObjectRestriction.native_identity
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRestriction.composeSentence) := ObjectRestriction.native_compose

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectRestriction.functionSentence := ObjectRestriction.source_ZF_function
example : FirstOrder.Derives (TheoryTransport.theory ObjectRestriction.assumptions) []
    (Translation.sentence ObjectRestriction.functionSentence) := ObjectRestriction.function_kernel_certificate

example {n} (b d : Fin n) : Source.SetLanguage.subset b d = RestrictionSyntax.subset b d := RestrictionSyntax.subset_original b d

/-- 返回完整原functionOn，子域条件也使用原subset，均未作弱化。 -/
theorem restriction_is_original_function {n} {Γ : Source.Context n} (g f d b : Fin n)
    (hf : Source.Derives Γ (Source.SetLanguage.functionOn f d))
    (hb : Source.Derives Γ (Source.SetLanguage.subset b d))
    (hr : Source.Derives Γ (RestrictionSyntax.restrict g f b)) : Source.Derives Γ (Source.SetLanguage.functionOn g b) := by
  rw [GraphSyntax.functionOn_original] at hf ⊢
  rw [RestrictionSyntax.subset_original] at hb
  exact RestrictionFunction.function_restrict g f d b hf hb hr

/-- 相同变量槽的子域限制，不暗加b与d不同的条件。 -/
def selfRestrictionSentence : Source.Sentence :=
  ((GraphSyntax.functionOn (0 : Fin 2) 1).imp (RestrictionSyntax.existsRestriction 0 1)).close

theorem self_restriction : FirstOrder.Derives nativeZF [] (Translation.sentence selfRestrictionSentence) := by
  apply ObjectRestriction.native_replay
  apply TheoryTransport.sentence
  apply SourceAlgebra.close_derives
  apply Source.Derives.impI
  have he : Source.Derives (ObjectRestriction.assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Source.Derives (ObjectRestriction.assumptions.at 2)
      ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  have hb : Source.Derives (Source.Context.add (GraphSyntax.functionOn 0 1) (ObjectRestriction.assumptions.at 2))
      (RestrictionSyntax.subset (1 : Fin 2) 1) := .allI (.impI (.hyp (Or.inl rfl)))
  exact RestrictionExistence.exists_function_restriction 0 1 1 (SourceLogic.add hs _) (SourceLogic.add he _) (.hyp (Or.inl rfl)) hb
/-- 任意内部集合族并图与实际定义域的六个原核闭句，包含空族。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.domainSentence) := ObjectGraphFamily.native_domain
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.domainUniqueSentence) := ObjectGraphFamily.native_domain_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.unionSentence) := ObjectGraphFamily.native_union
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.uniqueSentence) := ObjectGraphFamily.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.edgeSentence) := ObjectGraphFamily.native_edge
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphFamily.emptySentence) := ObjectGraphFamily.native_empty

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectGraphFamily.unionSentence := ObjectGraphFamily.source_ZF_union
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphFamily.assumptions) []
    (Translation.sentence ObjectGraphFamily.unionSentence) := ObjectGraphFamily.union_kernel_certificate

/-- 返回完整原functionOn，不把相容族并图弱化为单值关系。 -/
theorem family_union_is_original_function {n} {Γ : Source.Context n} (g d f : Fin n)
    (hu : Source.Derives Γ (InsertSyntax.unionOf g f)) (hd : Source.Derives Γ (GraphDomainSyntax.domain d g))
    (hf : Source.Derives Γ (GraphFamilySyntax.graphs f)) (hc : Source.Derives Γ (GraphFamilySyntax.compatible f)) :
    Source.Derives Γ (Source.SetLanguage.functionOn g d) := by
  rw [GraphSyntax.functionOn_original]
  exact GraphFamilyFunction.function_on g d f hu hd hf hc

/-- 输入界直接针对原Kuratowski/edge，不假设外部秩、良基或图有限。 -/
theorem edge_input_in_double_union {n} {Γ : Source.Context n} (g u v x y : Fin n)
    (hu : Source.Derives Γ (InsertSyntax.unionOf u g)) (hv : Source.Derives Γ (InsertSyntax.unionOf v u))
    (he : Source.Derives Γ (Source.SetLanguage.edge g x y)) : Source.Derives Γ (.mem x v) := by
  rw [GraphSyntax.edge_original] at he
  exact GraphDomainBound.edge_bound g u v x y hu hv he
/-- 原Infinity严格接入对象归纳集，未将宿主Nat作为对象ω。 -/
example : Source.SetLanguage.infinity = .ex (OmegaSyntax.isInductive (0 : Fin 1)) := OmegaSyntax.infinity_original

example : FirstOrder.Derives nativeZF [] (Translation.sentence OmegaSyntax.omegaExists) := ObjectOmega.native_existence
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmega.uniqueSentence) := ObjectOmega.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmega.characterizationSentence) := ObjectOmega.native_characterization
example : Source.Derives (Source.SetLanguage.ZF.at 0) OmegaSyntax.omegaExists := ObjectOmega.source_ZF_existence

/-- 每个任意公式模式索引都有实际全参数闭句及原核推导。 -/
theorem all_object_omega_induction {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (OmegaInductionSyntax.sentence p)) := OmegaInduction.native_induction p

example {n} (p : Source.Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (OmegaInductionSyntax.sentence p) := OmegaInduction.source_ZF_induction p

/-- 归纳逻辑核心只用该矩阵的一个分离实例；存在性三公理证书另行验收。 -/
example {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory (OmegaInduction.assumptions p)) []
      (Translation.sentence (OmegaInductionSyntax.sentence p)) := OmegaInduction.kernel_certificate p

example : FirstOrder.Derives (TheoryTransport.theory ObjectOmega.assumptions) []
    (Translation.sentence OmegaSyntax.omegaExists) := ObjectOmega.existence_kernel_certificate

/-- 多参数、交错对象量词的实际归纳模式实例。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence (OmegaInductionSyntax.sentence parameterMatrix)) :=
  OmegaInduction.native_induction parameterMatrix
/-- 全部内部集合不自属，不预设宿主成员关系良基。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectIrreflexivity.sentence) := ObjectIrreflexivity.native_proof

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.decompositionSentence) := ObjectOmegaStructure.native_decomposition

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.transitiveSentence) := ObjectOmegaStructure.native_transitive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.elementsSentence) := ObjectOmegaStructure.native_elements

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.zeroSentence) := ObjectOmegaStructure.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.successorSentence) := ObjectOmegaStructure.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.nonzeroSentence) := ObjectOmegaStructure.native_nonzero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.injectiveSentence) := ObjectOmegaStructure.native_injective

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOmegaStructure.freshSentence) := ObjectOmegaStructure.native_fresh

/-- 结构证书的有限公理集合没有加入Infinity、Replacement、Collection或AC。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectOmegaStructure.assumptions) []
    (Translation.sentence ObjectOmegaStructure.injectiveSentence) := ObjectOmegaStructure.injective_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectOmegaStructure.freshSentence := ObjectOmegaStructure.source_ZF_fresh

/-- 全对象成员版本：归纳结果直接提供图扩展所需的新输入不自属见证。 -/
theorem internal_fresh_successor {n} {Γ : Source.Context n} (w x : Fin n)
    (hf : Source.Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Source.Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hw : Source.Derives Γ (OmegaSyntax.omega w)) (hx : Source.Derives Γ (.mem x w)) :
    Source.Derives Γ (ObjectOmegaStructure.freshSuccessor w x) := ObjectOmegaStructure.fresh_successor w x hf hp hw hx

/-- 任意集合图的全部成员由原entriesOn约束，逐边相同推出真正的图相等。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.subsetSentence) := ObjectGraphPointwise.native_subset

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.edgesSentence) := ObjectGraphPointwise.native_edges

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.inclusionSentence) := ObjectGraphPointwise.native_inclusion

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.equalitySentence) := ObjectGraphPointwise.native_equality

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.domainSentence) := ObjectGraphPointwise.native_domain

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGraphPointwise.domainUniqueSentence) := ObjectGraphPointwise.native_domainUnique

/-- 外延性单公理证书不引入选择或任何Collection/Replacement实例。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectGraphPointwise.assumptions) []
    (Translation.sentence ObjectGraphPointwise.equalitySentence) := ObjectGraphPointwise.equality_kernel_certificate

/-- 开放版本保留任意内部域包含，供有限迭代图的前缀一致性证明使用。 -/
theorem compatible_graph_subset {n} {Γ : Source.Context n} (f g d e : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Source.Derives Γ (GraphSyntax.functionOn f d)) (hg : Source.Derives Γ (GraphSyntax.functionOn g e))
    (hd : Source.Derives Γ (RestrictionSyntax.subset d e)) (ha : Source.Derives Γ (GraphFamilySyntax.agrees f g)) :
    Source.Derives Γ (RestrictionSyntax.subset f g) := GraphPointwise.subset_of_agrees f g d e he hf hg hd ha

/-- 轨迹实际包含原functionOn和全部对象输入/输出的并集递推约束。 -/
example {n} (f d z a : Fin n) : IterationSyntax.track f d z a =
    (GraphSyntax.functionOn f d).conj ((GraphSyntax.edge f z a).conj (IterationSyntax.next f)) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectIterationUniqueness.commonSentence) := ObjectIterationUniqueness.native_common

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectIterationUniqueness.compatibleSentence) := ObjectIterationUniqueness.native_compatible

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectIterationUniqueness.uniqueSentence) := ObjectIterationUniqueness.native_unique

/-- 两公理核心证书不调用Collection/Replacement，结论是给定轨迹的唯一性。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectIterationUniqueness.assumptions) []
    (Translation.sentence ObjectIterationUniqueness.uniqueSentence) := ObjectIterationUniqueness.unique_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectIterationUniqueness.commonSentence := ObjectIterationUniqueness.source_ZF_common

/-- 全部内部ω成员上的共同输入模式，不以外部标准长度列表代替。 -/
theorem tracks_agree_on_all_internal_inputs {n} {Γ : Source.Context n} (f g d e z a w : Fin n)
    (he : Source.Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Source.Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix).rename Fin.elim0))
    (hw : Source.Derives Γ (OmegaSyntax.omega w)) (hz : Source.Derives Γ (OmegaSyntax.empty z))
    (hf : Source.Derives Γ (IterationSyntax.track f d z a)) (hg : Source.Derives Γ (IterationSyntax.track g e z a))
    (hd : Source.Derives Γ (OmegaStructureSyntax.transitive d)) (hc : Source.Derives Γ (OmegaStructureSyntax.transitive e)) :
    Source.Derives Γ (IterationSyntax.allCommon f g d e w) := IterationInduction.all_common f g d e z a w he hs hw hz hf hg hd hc

/-- 实际有限轨迹的域是对象长度的后继，图保留完整原functionOn及递推规律。 -/
example {n} (f d k z a : Fin n) : FiniteIterationSyntax.witness f d k z a =
    (OmegaSyntax.successor d k).conj (IterationSyntax.track f d z a) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectFiniteIteration.baseSentence) := ObjectFiniteIteration.native_base

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectFiniteIteration.existenceSentence) := ObjectFiniteIteration.native_existence

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectFiniteIteration.uniquenessSentence) := ObjectFiniteIteration.native_uniqueness

/-- 存在结论已覆盖全部内部ω长度，且有源Replacement版ZF的实际推导。 -/
example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectFiniteIteration.existenceSentence := ObjectFiniteIteration.source_ZF_existence

/-- 八句有限公理理论内的原核证书；未调用Replacement、Collection或对象AC。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectFiniteIteration.assumptions) []
    (Translation.sentence ObjectFiniteIteration.existenceSentence) := ObjectFiniteIteration.existence_kernel_certificate

example : FirstOrder.Derives (TheoryTransport.theory ObjectFiniteIteration.assumptions) []
    (Translation.sentence ObjectFiniteIteration.uniquenessSentence) := ObjectFiniteIteration.uniqueness_kernel_certificate

/-- 每个末值必须由实际有限轨迹见证，不以宿主迭代函数替代。 -/
example {n} (f d k z a r : Fin n) {Γ : Source.Context n}
    (hf : Source.Derives Γ (FiniteIterationSyntax.witness f d k z a)) (hr : Source.Derives Γ (GraphSyntax.edge f k r)) :
    Source.Derives Γ (IterationValueSyntax.value k z a r) := IterationValueSyntax.intro_value f d k z a r hf hr

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectTransitiveCover.rangeSentence) := ObjectTransitiveCover.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectTransitiveCover.propertiesSentence) := ObjectTransitiveCover.native_properties

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectTransitiveCover.coverSentence) := ObjectTransitiveCover.native_cover

/-- 原Replacement版ZF中真正的全对象传递覆盖；不存在Collection前提。 -/
example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectTransitiveCover.coverSentence := ObjectTransitiveCover.source_cover

example : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence ObjectTransitiveCover.coverSentence) := ObjectTransitiveCover.cover_kernel_certificate

/-- 完整闭句的对象内容，全部集合a都存在实际传递覆盖b。 -/
example : ObjectTransitiveCover.coverSentence =
    (TransitiveCoverSyntax.coverExists (0 : Fin 1)).close := rfl

/-- 两个任意公式模式的每个实例都有全参数闭句及原核推导。 -/
theorem all_object_set_induction {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (SetInductionSyntax.sentence p)) := SetInduction.native_induction p

theorem all_object_global_member_minimal {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (GlobalMinimalSyntax.sentence p)) := GlobalMinimal.native_minimal p

example {n} (p : Source.Formula (n+1)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (SetInductionSyntax.sentence p) := SetInduction.source_induction p

example {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (GlobalMinimalSyntax.sentence p)) := GlobalMinimal.kernel_certificate p

/-- 任意参数与交错对象量词实例，并包含无参数实例。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence (SetInductionSyntax.sentence parameterMatrix)) :=
  SetInduction.native_induction parameterMatrix

example : FirstOrder.Derives nativeZF [] (Translation.sentence (GlobalMinimalSyntax.sentence parameterMatrix)) :=
  GlobalMinimal.native_minimal parameterMatrix

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (SetInductionSyntax.sentence (Source.Formula.equal (0 : Fin 1) 0))) :=
  SetInduction.native_induction _

example : FirstOrder.Derives nativeZF []
    (Translation.sentence (GlobalMinimalSyntax.sentence (Source.Formula.equal (0 : Fin 1) 0))) :=
  GlobalMinimal.native_minimal _

/-- 原序数与其全部内部子集良基条件严格保持，未改成宿主WellFounded。 -/
example {n} (a : Fin n) : Source.SetLanguage.ordinal a = OrdinalSyntax.ordinal a := rfl
example {n} (a : Fin n) : Source.SetLanguage.membershipLinear a = OrdinalSyntax.linear a := rfl
example {n} (a : Fin n) : Source.SetLanguage.membershipWellFounded a = OrdinalSyntax.wellFounded a := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.wellFoundedSentence) := ObjectOrdinalBasic.native_wellFounded

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.noSelfSentence) := ObjectOrdinalBasic.native_noSelf

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.emptySentence) := ObjectOrdinalBasic.native_empty

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.memberSentence) := ObjectOrdinalBasic.native_member

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.successorSentence) := ObjectOrdinalBasic.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.existsEmptySentence) := ObjectOrdinalBasic.native_existsEmpty

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalBasic.existsSuccessorSentence) := ObjectOrdinalBasic.native_existsSuccessor

/-- 直接使用原Source.ordinal的实际原核成员闭包接口。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (((Source.SetLanguage.ordinal (0 : Fin 2)).imp ((Source.Formula.mem 1 0).imp (Source.SetLanguage.ordinal 1))).close)) := by
  simpa only [ObjectOrdinalBasic.memberSentence, OrdinalSyntax.ordinal_original] using ObjectOrdinalBasic.native_member

/-- 基础有限理论只含Foundation、EmptySet、Pairing和Union。 -/
example : FirstOrder.Derives (TheoryTransport.theory ObjectOrdinalBasic.assumptions) []
    (Translation.sentence ObjectOrdinalBasic.existsSuccessorSentence) := ObjectOrdinalBasic.existsSuccessor_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectOrdinalBasic.existsEmptySentence := ObjectOrdinalBasic.source_ZF_existsEmpty

/-- 任意两个原Source.ordinal的比较，所有集合参数均在完整闭句内。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (((Source.SetLanguage.ordinal (0 : Fin 2)).imp ((Source.SetLanguage.ordinal 1).imp
      ((Source.Formula.equal 0 1).disj ((Source.Formula.mem 0 1).disj (.mem 1 0))))).close)) := by
  simpa only [ObjectOrdinalComparison.comparisonSentence, OrdinalComparison.comparison,
    OrdinalSyntax.ordinal_original] using ObjectOrdinalComparison.native_comparison

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalComparison.differenceSentence) := ObjectOrdinalComparison.native_difference
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalComparison.initialSentence) := ObjectOrdinalComparison.native_initial
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalComparison.trichotomySentence) := ObjectOrdinalComparison.native_trichotomy
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalComparison.subsetSentence) := ObjectOrdinalComparison.native_subset
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalComparison.asymmetricSentence) := ObjectOrdinalComparison.native_asymmetric

/-- 三分支的排斥也在对象公式内；不是Lean中对集合分类。 -/
example {n} (a b : Fin n) : OrdinalTrichotomy.trichotomy a b =
    (OrdinalComparison.comparison a b).conj
      (((Source.Formula.equal a b).imp ((Source.Formula.mem a b).neg.conj (Source.Formula.mem b a).neg)).conj
        ((Source.Formula.mem a b).imp (Source.Formula.mem b a).neg)) := rfl

example : FirstOrder.Derives (TheoryTransport.theory ObjectOrdinalComparison.assumptions) []
    (Translation.sentence ObjectOrdinalComparison.trichotomySentence) := ObjectOrdinalComparison.trichotomy_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectOrdinalComparison.comparisonSentence := ObjectOrdinalComparison.source_ZF_comparison

/-- 比较所需有限理论精确为外延、Foundation和正文x∉b的一个分离实例。 -/
example (q : Source.Sentence) : ObjectOrdinalComparison.assumptions q ↔
    (q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.foundation ∨
      q = Source.SetLanguage.separation OrdinalDifference.outsideMatrix) := Iff.rfl

/-- 任意内部序数族的并，直接检查原Source.ordinal而非宿主Ordinal。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (((OrdinalFamilySyntax.ordinals (0 : Fin 2)).imp
      ((InsertSyntax.unionOf 1 0).imp (Source.SetLanguage.ordinal 1))).close)) := by
  simpa only [ObjectOrdinalUnion.unionSentence, OrdinalSyntax.ordinal_original] using ObjectOrdinalUnion.native_union

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalUnion.familySentence) := ObjectOrdinalUnion.native_family
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalUnion.leastSentence) := ObjectOrdinalUnion.native_least
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalUnion.uniqueSentence) := ObjectOrdinalUnion.native_unique
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalUnion.existenceSentence) := ObjectOrdinalUnion.native_existence
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectOrdinalUnion.strictSentence) := ObjectOrdinalUnion.native_strict

/-- 最小性量化全部内部集合上界；不额外要求该上界是序数。 -/
example {n} (u c : Fin n) : OrdinalFamilySyntax.leastUpper u c =
    (OrdinalFamilySyntax.upperBound c u).conj (.all
      ((OrdinalFamilySyntax.upperBound c.castSucc (Fin.last n)).imp
        (RestrictionSyntax.subset u.castSucc (Fin.last n)))) := rfl

/-- 序数族参数是一个内部集合；未限制外部有限、可数、非空或序数已给界。 -/
example {n} (c : Fin n) : OrdinalFamilySyntax.ordinals c = .all
    ((Source.Formula.mem (Fin.last n) c.castSucc).imp (Source.SetLanguage.ordinal (Fin.last n))) := rfl

example : FirstOrder.Derives (TheoryTransport.theory ObjectOrdinalUnion.assumptions) []
    (Translation.sentence ObjectOrdinalUnion.existenceSentence) := ObjectOrdinalUnion.existence_kernel_certificate
example : FirstOrder.Derives (TheoryTransport.theory ObjectOrdinalUnion.strictAssumptions) []
    (Translation.sentence ObjectOrdinalUnion.strictSentence) := ObjectOrdinalUnion.strict_kernel_certificate
example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectOrdinalUnion.strictSentence := ObjectOrdinalUnion.source_ZF_strict

/-- 严格上界必须含族中每个序数作为成员；仅证明子集上界不足以通过此接口。 -/
example {n} (c b : Fin n) : OrdinalStrictBound.strictUpper c b = .all
    ((Source.Formula.mem (Fin.last n) c.castSucc).imp (.mem (Fin.last n) b.castSucc)) := rfl

/-- 每个任意三元递推矩阵及任意参数数目，均有完整对象闭句和原核证书。 -/
theorem all_recursion_preservation {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.preservationSentence p)) := ObjectOrdinalRecursion.native_preservation p

theorem all_recursion_restrictions {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.restrictionSentence p)) := ObjectOrdinalRecursion.native_restriction p

theorem all_given_recursors_compatible {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.compatibilitySentence p)) := ObjectOrdinalRecursion.native_compatibility p

theorem all_given_recursors_unique {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.uniquenessSentence p)) := ObjectOrdinalRecursion.native_uniqueness p

/-- 两个参数、索引/历史/输出和交错对象量词；不是仅检验固定无参数矩阵。 -/
def recursionMatrix : Source.Formula 5 := (Source.Formula.mem 2 0).conj (.all
    ((Source.Formula.mem (Fin.last 5) (3 : Fin 5).castSucc).imp (.ex
      ((Source.Formula.mem (Fin.last 6) (1 : Fin 5).castSucc.castSucc).conj
        (.equal (Fin.last 5).castSucc (4 : Fin 5).castSucc.castSucc)))))

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.compatibilitySentence recursionMatrix)) :=
  ObjectOrdinalRecursion.native_compatibility recursionMatrix
example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursion.restrictionSentence recursionMatrix)) :=
  ObjectOrdinalRecursion.native_restriction recursionMatrix
example : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectOrdinalRecursion.uniquenessSentence (Source.Formula.equal (2 : Fin 3) 0))) :=
  ObjectOrdinalRecursion.native_uniqueness _

/-- 每步显式存在真实历史集合；完整原functionOn保留entriesOn与总单值性。 -/
example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) :
    OrdinalRecursionSyntax.recursor p ρ f d =
      (Source.SetLanguage.functionOn f d).conj (OrdinalRecursionSyntax.equations p ρ f d) := by
  rw [GraphSyntax.functionOn_original]
  rfl

example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (f x y : Fin m) :
    OrdinalRecursionSyntax.history p ρ f x y = .ex
      ((RestrictionSyntax.restrict (Fin.last m) f.castSucc x.castSucc).conj
        (OrdinalRecursionSyntax.operator p (ReplacementPredicates.paramsUp ρ) x.castSucc (Fin.last m) y.castSucc)) := rfl

example {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives (TheoryTransport.theory ObjectOrdinalRecursion.assumptions) []
      (Translation.sentence (ObjectOrdinalRecursion.compatibilitySentence p)) := ObjectOrdinalRecursion.compatibility_kernel_certificate p

example {n} (p : Source.Formula (n+3)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (ObjectOrdinalRecursion.uniquenessSentence p) := ObjectOrdinalRecursion.source_ZF_uniqueness p

/-- 总性只要求全部内部有效序数/完整前段图，不假设宿主递推函数。 -/
example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) : OrdinalRecursionTotal.total p ρ = .all (.all
    (((Source.SetLanguage.ordinal (Fin.last m).castSucc).conj
      (GraphSyntax.functionOn (Fin.last (m+1)) (Fin.last m).castSucc)).imp
        (OrdinalRecursionTotal.hasValue p (ReplacementPredicates.paramsUp (ReplacementPredicates.paramsUp ρ))
          (Fin.last m).castSucc (Fin.last (m+1))))) := rfl

/-- 每个任意矩阵实例均返回完整对象闭句及原核证书。 -/
theorem all_recursion_successor_evaluation {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.evaluationSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_evaluation p

theorem all_recursion_successor_preservation {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.preservationSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_preservation p

theorem all_recursion_successor_extension {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.extensionSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_extension p

theorem all_recursion_successor_successor {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.successorSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_successor p

theorem all_recursion_successor_unique {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.uniqueSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_unique p

theorem all_recursion_successor_fiber {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.fiberSentence p)) :=
  ObjectOrdinalRecursionSuccessor.native_fiber p

/-- 先前的双参数交错量词矩阵及无参数实例均可接入本批。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.extensionSentence recursionMatrix)) :=
  ObjectOrdinalRecursionSuccessor.native_extension recursionMatrix
example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectOrdinalRecursionSuccessor.fiberSentence recursionMatrix)) :=
  ObjectOrdinalRecursionSuccessor.native_fiber recursionMatrix
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectOrdinalRecursionSuccessor.successorSentence (Source.Formula.equal (2 : Fin 3) 0))) :=
  ObjectOrdinalRecursionSuccessor.native_successor _

/-- 实际扩展须保留旧图作为旧域限制，且返回后继序数及完整递归图。 -/
example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (g s f d : Fin m) :
    OrdinalRecursionSuccessorSyntax.extension p ρ g s f d =
      (OmegaSyntax.successor s d).conj ((Source.SetLanguage.ordinal s).conj
        ((OrdinalRecursionSyntax.recursor p ρ g s).conj (RestrictionSyntax.restrict f g d))) := rfl

/-- 原Replacement接口精确接收实际唯一后继图，不能用存在旧图或条件唯一替代纤维。 -/
example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) :
    ReplacementPredicates.fiber (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ d =
      OrdinalRecursionSuccessorUnique.uniqueFiber p ρ d := OrdinalRecursionSuccessorUnique.matrix_fiber p ρ d

example {n} (p : Source.Formula (n+3)) : FirstOrder.Derives
    (TheoryTransport.theory ObjectOrdinalRecursionSuccessor.assumptions) []
      (Translation.sentence (ObjectOrdinalRecursionSuccessor.fiberSentence p)) :=
  ObjectOrdinalRecursionSuccessor.fiber_kernel_certificate p

example {n} (p : Source.Formula (n+3)) :
    Source.Derives (Source.SetLanguage.ZF.at 0) (ObjectOrdinalRecursionSuccessor.extensionSentence p) :=
  ObjectOrdinalRecursionSuccessor.source_ZF_extension p

/-- 全对象超限递归：每个矩阵实例均覆盖全部内部原序数，实际存在与唯一均已证明。 -/
theorem all_transfinite_recursion_collection {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectTransfiniteRecursion.collectionSentence p)) :=
  ObjectTransfiniteRecursion.native_collection p

theorem all_transfinite_recursion_union {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectTransfiniteRecursion.unionSentence p)) :=
  ObjectTransfiniteRecursion.native_union p

theorem all_transfinite_recursion_existence {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectTransfiniteRecursion.existenceSentence p)) :=
  ObjectTransfiniteRecursion.native_existence p

theorem all_transfinite_recursion_uniqueness {n} (p : Source.Formula (n+3)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectTransfiniteRecursion.uniquenessSentence p)) :=
  ObjectTransfiniteRecursion.native_uniqueness p

/-- 直接核对原Source.ordinal与完整内部全称-存在量词，避免把外部标准实例当全序数递归。 -/
example {n} (p : Source.Formula (n+3)) : ObjectTransfiniteRecursion.existenceSentence p =
    ((OrdinalRecursionTotal.total p (id : Fin n → Fin n)).imp
      ((OrdinalRecursionDeterminism.deterministic p id).imp (.all
        ((Source.SetLanguage.ordinal (Fin.last n)).imp
          (OrdinalRecursionSyntax.recursorExists p Fin.castSucc (Fin.last n)))))).close := rfl

example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) :
    OrdinalRecursionExistenceSyntax.fiber p ρ a = .ex
      ((OrdinalRecursionSyntax.recursor p (ReplacementPredicates.paramsUp ρ) (Fin.last m) a.castSucc).conj
        (OrdinalRecursionExistenceSyntax.uniqueAt p (ReplacementPredicates.paramsUp ρ) a.castSucc (Fin.last m))) := rfl

/-- 实际收集族同时保留精确像和逐内部前驱覆盖，没有假设所有候选图构成集合。 -/
example {n m} (p : Source.Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) :
    OrdinalRecursionFamilySyntax.family p ρ c a =
      (OrdinalRecursionFamilySyntax.range p ρ c a).conj (OrdinalRecursionFamilySyntax.coverage p ρ c a) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectTransfiniteRecursion.uniquenessSentence recursionMatrix)) :=
  ObjectTransfiniteRecursion.native_uniqueness recursionMatrix
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectTransfiniteRecursion.existenceSentence (Source.Formula.equal (2 : Fin 3) 0))) := ObjectTransfiniteRecursion.native_existence _

/-- 具体算子y=x已实际消去总性/单值性前提，仍覆盖全部内部原序数。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectTransfiniteRecursionIdentity.sentence) :=
  ObjectTransfiniteRecursionIdentity.native_proof

example {n} (p : Source.Formula (n+3)) : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence (ObjectTransfiniteRecursion.uniquenessSentence p)) := ObjectTransfiniteRecursion.uniqueness_kernel_certificate p

example {n} (p : Source.Formula (n+3)) : Source.Derives (Source.SetLanguage.ZF.at 0)
    (ObjectTransfiniteRecursion.existenceSentence p) := ObjectTransfiniteRecursion.source_existence p

/-- 原幂集公理严格对应；所有子集量词在对象语言内。 -/
example : Source.SetLanguage.powerSet = (PowerSetSyntax.powerExists (0 : Fin 1)).close := PowerSetSyntax.power_core

example {n} (w v : Fin n) : PowerSetSyntax.powerOf w v = .all
    ((Source.Formula.mem (Fin.last n) w.castSucc).iff (Source.SetLanguage.subset (Fin.last n) v.castSucc)) := rfl

/-- 实际历史幂集像集合和实际Union见证，不用宿主powerset运算符。 -/
example {n} (a h y : Fin n) : PowerUnionSyntax.operation a h y = .ex
    ((PowerValueSyntax.range (Fin.last n) a.castSucc h.castSucc).conj (InsertSyntax.unionOf y.castSucc (Fin.last n))) := rfl

example {n} (ρ : Fin 0 → Fin n) (a h y : Fin n) :
    OrdinalRecursionSyntax.operator PowerUnionSyntax.matrix ρ a h y = PowerUnionSyntax.operation a h y :=
  PowerUnionSyntax.matrix_operator ρ a h y

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPowerUnion.rangeSentence) := ObjectPowerUnion.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPowerUnion.operationSentence) := ObjectPowerUnion.native_operation

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPowerUnion.totalSentence) := ObjectPowerUnion.native_total

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectPowerUnion.deterministicSentence) := ObjectPowerUnion.native_deterministic

/-- 层序列的总性/单值性前提已经由原ZF中的真实证明消去。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence HierarchyRecursion.existenceSentence) := HierarchyRecursion.native_existence
example : FirstOrder.Derives nativeZF [] (Translation.sentence HierarchyRecursion.uniquenessSentence) := HierarchyRecursion.native_uniqueness

/-- 直接使用原Source.ordinal检查全部内部序数的实际唯一层值。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (((Source.SetLanguage.ordinal (0 : Fin 1)).imp (HierarchyLayerSyntax.layerFiber 0)).close)) := by
  simpa only [ObjectCumulativeHierarchy.uniquenessSentence, OrdinalSyntax.ordinal_original] using ObjectCumulativeHierarchy.native_uniqueness

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectCumulativeHierarchy.existenceSentence) := ObjectCumulativeHierarchy.native_existence
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectCumulativeHierarchy.equalitySentence) := ObjectCumulativeHierarchy.native_equality
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectCumulativeHierarchy.zeroSentence) := ObjectCumulativeHierarchy.native_zero

/-- 层值由实际后继域上的完整递归图及真实输出边见证；不存在宿主序数索引。 -/
example {n} (a y : Fin n) : HierarchyLayerSyntax.layer a y = .ex (.ex
    (HierarchyLayerSyntax.data (Fin.last n).castSucc (Fin.last (n+1)) a.castSucc.castSucc y.castSucc.castSucc)) := rfl

example : FirstOrder.Derives (TheoryTransport.theory ObjectPowerUnion.assumptions) []
    (Translation.sentence ObjectPowerUnion.totalSentence) := ObjectPowerUnion.total_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectCumulativeHierarchy.uniquenessSentence := ObjectCumulativeHierarchy.source_uniqueness


/-- 历史输出等价覆盖任意内部原序数和每个内部早期索引；没有外部标准索引。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (((Source.SetLanguage.ordinal (0 : Fin 4)).imp ((HierarchyLayerSyntax.graph 1 0).imp
      ((Source.Formula.mem 2 0).imp ((GraphSyntax.edge 1 2 3).iff (HierarchyLayerSyntax.layer 2 3))))).close)) := by
  simpa only [ObjectHierarchyAlgebra.historySentence, OrdinalSyntax.ordinal_original] using ObjectHierarchyAlgebra.native_history

/-- 完整双存在见证：β∈α、实际Layer(β,v)和全部内部子集量词。 -/
example {m} (a z : Fin m) : HierarchyMemberSyntax.layerMember a z = .ex (.ex
    ((Source.Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
      ((HierarchyLayerSyntax.layer (Fin.last m).castSucc (Fin.last (m+1))).conj
        (Source.SetLanguage.subset z.castSucc.castSucc (Fin.last (m+1)))))) := rfl

example : ObjectHierarchyAlgebra.membershipSentence = ((OrdinalSyntax.ordinal (0 : Fin 2)).imp
    ((HierarchyLayerSyntax.layer 0 1).imp (.all ((Source.Formula.mem (Fin.last 2) (1 : Fin 2).castSucc).iff
      (HierarchyMemberSyntax.layerMember (0 : Fin 2).castSucc (Fin.last 2)))))).close := rfl

/-- 后继层结论是全内部子集式PowerOf，不以宿主幂集等式代替。 -/
example : ObjectHierarchyAlgebra.successorSentence = ((OrdinalSyntax.ordinal (0 : Fin 4)).imp
    ((OmegaSyntax.successor 1 0).imp ((HierarchyLayerSyntax.layer 0 2).imp
      ((HierarchyLayerSyntax.layer 1 3).imp (.all
        ((Source.Formula.mem (Fin.last 4) (3 : Fin 4).castSucc).iff
          (Source.SetLanguage.subset (Fin.last 4) (2 : Fin 4).castSucc))))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.historySentence) :=
  ObjectHierarchyAlgebra.native_history

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.operationSentence) :=
  ObjectHierarchyAlgebra.native_operation

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.membershipSentence) :=
  ObjectHierarchyAlgebra.native_membership

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.monotoneSentence) :=
  ObjectHierarchyAlgebra.native_monotone

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.memberSentence) :=
  ObjectHierarchyAlgebra.native_member

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.transitiveSentence) :=
  ObjectHierarchyAlgebra.native_transitive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyAlgebra.successorSentence) :=
  ObjectHierarchyAlgebra.native_successor

example : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence ObjectHierarchyAlgebra.transitiveSentence) := ObjectHierarchyAlgebra.transitive_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectHierarchyAlgebra.successorSentence := ObjectHierarchyAlgebra.source_successor


/-- 零或极限条件量化全部内部前驱，且实际存在其原后继。 -/
example {m} (a : Fin m) : HierarchyLimitSyntax.limitIndex a =
    (Source.SetLanguage.ordinal a).conj (.all ((Source.Formula.mem (Fin.last m) a.castSucc).imp (.ex
      ((Source.SetLanguage.successor (Fin.last (m+1)) (Fin.last m).castSucc).conj
        (.mem (Fin.last (m+1)) a.castSucc.castSucc))))) := rfl

/-- 极限成员式的每个早层值均为实际内部见证，全部内部量词保留。 -/
example {m} (a z : Fin m) : HierarchyLimitSyntax.unionMember a z = .ex (.ex
    ((Source.Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
      ((HierarchyLayerSyntax.layer (Fin.last m).castSucc (Fin.last (m+1))).conj
        (.mem z.castSucc.castSucc (Fin.last (m+1)))))) := rfl

/-- 精确Replacement像与原UnionOf的实际集合见证，不只有类成员描述。 -/
example {m} (a y : Fin m) : HierarchyFamilySyntax.assembled a y = .ex
    ((HierarchyFamilySyntax.range (Fin.last m) a.castSucc).conj (InsertSyntax.unionOf y.castSucc (Fin.last m))) := rfl

example {m} (ρ : Fin 0 → Fin m) (b : Fin m) :
    ReplacementPredicates.fiber HierarchyFamilySyntax.matrix ρ b = HierarchyLayerSyntax.layerFiber b :=
  HierarchyFamilySyntax.matrix_fiber ρ b

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.equationSentence) :=
  ObjectHierarchyLimit.native_equation

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.rangeSentence) :=
  ObjectHierarchyLimit.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.rangeEqualitySentence) :=
  ObjectHierarchyLimit.native_rangeEquality

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.unionSentence) :=
  ObjectHierarchyLimit.native_union

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.assembledSentence) :=
  ObjectHierarchyLimit.native_assembled

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectHierarchyLimit.zeroSentence) :=
  ObjectHierarchyLimit.native_zero

/-- 任意外部有限参数数目及任意公式实例都给完整闭句与实际原核证明。 -/
example {n} (p : Source.Formula (n+1)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectOrdinalLeast.uniquenessSentence p)) := ObjectOrdinalLeast.native_uniqueness p

example {n} (p : Source.Formula (n+1)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectOrdinalLeast.existenceSentence p)) := ObjectOrdinalLeast.native_existence p

example {n} (p : Source.Formula (n+1)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectOrdinalLeast.equalitySentence p)) := ObjectOrdinalLeast.native_equality p

/-- 最小性比较全部内部满足同一原参数性质的序数，不是外部成员枚举。 -/
example {n m} (p : Source.Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) :
    OrdinalLeastSyntax.least p ρ a =
      ((Source.SetLanguage.ordinal a).conj (MinimalPredicates.pred p ρ a)).conj (.all
        (((Source.SetLanguage.ordinal (Fin.last m)).conj
          (MinimalPredicates.pred p (ReplacementPredicates.paramsUp ρ) (Fin.last m))).imp
          ((Source.Formula.equal a.castSucc (Fin.last m)).disj (.mem a.castSucc (Fin.last m))))) := rfl

example {n} (p : Source.Formula (n+1)) : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence (ObjectOrdinalLeast.uniquenessSentence p)) := ObjectOrdinalLeast.uniqueness_kernel_certificate p

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectOrdinalLeast.uniquenessSentence (Source.Formula.equal (0 : Fin 1) 0))) := ObjectOrdinalLeast.native_uniqueness _

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectHierarchyLimit.assembledSentence := ObjectHierarchyLimit.source_assembled


/-- 覆盖完整内部集合：实际序数、实际层值和全部内部子集量词。 -/
example {m} (x : Fin m) : LayerCoverSyntax.cover x = .ex
    ((Source.SetLanguage.ordinal (Fin.last m)).conj (.ex
      ((HierarchyLayerSyntax.layer (Fin.last m).castSucc (Fin.last (m+1))).conj
        (Source.SetLanguage.subset x.castSucc.castSucc (Fin.last (m+1)))))) := rfl

/-- 最终成员覆盖是∀x∃α∃v的完整句子，没有归纳前提残留。 -/
example {m} (x : Fin m) : LayerCoverSyntax.memberCover x = .ex (.ex
    ((Source.SetLanguage.ordinal (Fin.last m).castSucc).conj
      ((HierarchyLayerSyntax.layer (Fin.last m).castSucc (Fin.last (m+1))).conj
        (.mem x.castSucc.castSucc (Fin.last (m+1)))))) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    ((LayerCoverSyntax.memberCover (0 : Fin 1)).close)) := ObjectRankCover.native_member

/-- 秩性质精确为x⊆某个实际Vα；最小序数的参数仍为原内部x。 -/
example {m} (x a : Fin m) : LayerRankSyntax.rank x a =
    OrdinalLeastSyntax.least LayerCoverSyntax.containsMatrix (fun _ => x) a := rfl

example {m} (x a : Fin m) : OrdinalLeastSyntax.property LayerCoverSyntax.containsMatrix (fun _ => x) a =
    (Source.SetLanguage.ordinal a).conj (.ex
      ((HierarchyLayerSyntax.layer a.castSucc (Fin.last m)).conj
        (Source.SetLanguage.subset x.castSucc (Fin.last m)))) := LayerCoverSyntax.contains_property x a

/-- 原Replacement接收实际唯一秩纤维，精确像保留每个内部成员及其原秩关系。 -/
example {m} (ρ : Fin 0 → Fin m) (x : Fin m) :
    ReplacementPredicates.fiber LayerRankSyntax.matrix ρ x = LayerRankSyntax.fiber x := LayerRankSyntax.matrix_fiber ρ x

example {m} (ρ : Fin 0 → Fin m) (x c : Fin m) :
    ReplacementPredicates.exactImage LayerRankSyntax.matrix ρ x c = LayerRankSyntax.range c x := LayerRankSyntax.matrix_range ρ x c

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.coverSentence) :=
  ObjectRankCover.native_cover

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.rankSentence) :=
  ObjectRankCover.native_rank

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.memberSentence) :=
  ObjectRankCover.native_member

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.rangeSentence) :=
  ObjectRankCover.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.equalitySentence) :=
  ObjectRankCover.native_equality

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectRankCover.propertySentence) :=
  ObjectRankCover.native_property

example : FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence ObjectRankCover.memberSentence) := ObjectRankCover.member_kernel_certificate

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectRankCover.coverSentence := ObjectRankCover.source_cover

example : Source.Derives (Source.SetLanguage.ZF.at 0) ObjectRankCover.rankSentence := ObjectRankCover.source_rank

end PPAC.Migration.Step3Checks

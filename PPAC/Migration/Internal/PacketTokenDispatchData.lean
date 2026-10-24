import PPAC.Migration.Internal.PacketTokenApplication

/-! All eight non-token rules are classified from the pinned original Packet table. -/
namespace PPAC.Migration.Internal.PacketTokenDispatchData
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Rule)
open PacketTokenRuleData

def others : List Rule := ObjectPacket.rules.take 4 ++ ObjectPacket.rules.drop 6

theorem others_classified : others.all (fun r => PacketAffineDispatchData.differentOuter 2 r.head) = true := rfl

theorem others_different (rule : Rule) (hr : rule ∈ others) : PacketAffineDispatchData.differentOuter 2 rule.head = true :=
  List.all_eq_true.mp others_classified rule hr

theorem small_member : smallRule ∈ ObjectPacket.rules := by
  simp [smallRule,ObjectPacket.rules]

theorem large_member : largeRule ∈ ObjectPacket.rules := by
  simp [largeRule,ObjectPacket.rules]

theorem rule_cases (rule : Rule) (hr : rule ∈ ObjectPacket.rules) : rule = smallRule ∨ rule = largeRule ∨ rule ∈ others := by
  simp only [ObjectPacket.rules,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (by simp [others,ObjectPacket.rules]))

end PPAC.Migration.Internal.PacketTokenDispatchData

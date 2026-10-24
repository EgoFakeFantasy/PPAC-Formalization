import PPAC.Migration.Internal.ObjectPacketTokenBounds

/-! Four unchanged original structural rules and their exact arities and ordered fields. -/
namespace PPAC.Migration.Internal.PacketStructureRuleData
open YesMetaZFC.Automation
open ObjectHorn (Rule Expr)

def treeRule : Rule := ObjectPacket.treeRule
def nilRule : Rule := ObjectPacket.forestNil
def consRule : Rule := ObjectPacket.forestCons
def packetRule : Rule := ObjectPacket.packetRule

theorem tree_arity : treeRule.arity = 7 := rfl
theorem nil_arity : nilRule.arity = 1 := rfl
theorem cons_arity : consRule.arity = 6 := rfl
theorem packet_arity : packetRule.arity = 3 := rfl

theorem tree_head : treeRule.head = ObjectPacket.node (n := 7) 3 [ObjectPacket.rawNode (.var 0) (.var 1), .var 2, .var 3] := rfl
theorem nil_head : nilRule.head = ObjectPacket.node (n := 1) 4 [Expr.list [] , .literal 0, .var 0, .var 0] := rfl
theorem cons_head : consRule.head = ObjectPacket.node (n := 6) 4 [ObjectPacket.cons (.var 0) (.var 1), .succ (.var 2), .var 3, .var 4] := rfl
theorem packet_head : packetRule.head = ObjectPacket.node (n := 3) 5 [.var 1, .var 0] := rfl

theorem tree_guards : treeRule.guards = [] := rfl
theorem nil_guards : nilRule.guards = [] := rfl
theorem cons_guards : consRule.guards = [] := rfl
theorem packet_guards : packetRule.guards = [] := rfl

theorem tree_premises : treeRule.premises = [ObjectPacket.node (n := 7) 4 [.var 1, .var 4, .var 2, .var 5] , ObjectPacket.node 2 [.var 4, .var 5, .var 6] , ObjectPacket.node 2 [.var 0, .var 6, .var 3]] := rfl
theorem nil_premises : nilRule.premises = [] := rfl
theorem cons_premises : consRule.premises = [ObjectPacket.node (n := 6) 4 [.var 1, .var 2, .var 3, .var 5] , ObjectPacket.node 3 [.var 0, .var 5, .var 4]] := rfl
theorem packet_premises : packetRule.premises = [ObjectPacket.node (n := 3) 1 [.literal 1, .var 2, .var 1] , ObjectPacket.node 3 [.var 0, .literal 1, .var 2]] := rfl

end PPAC.Migration.Internal.PacketStructureRuleData

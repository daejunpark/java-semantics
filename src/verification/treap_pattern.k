// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TREAP-PATTERN
  imports MAP
  imports JAVA-EXEC
  imports INT-SET

  syntax PTree ::= "pnode" "(" Int /* Key */ "," Int /* Priority */ "," PTree "," PTree ")"
                 | "pleaf"

  syntax IntSet ::= "ptree_keys" "(" PTree ")"    [function, smtlib(smt_ptree_keys)]
  rule ptree_keys(pnode(I:Int, _, TL:PTree, TR:PTree)) => { I } U (ptree_keys(TL) U ptree_keys(TR))
  rule ptree_keys(pleaf) => .IntSet

  syntax Int ::= "ptree_max_priority" "(" PTree ")"    [function, smtlib(smt_ptree_max_priority)]
  rule ptree_max_priority(pnode(_, Z:Int, TL:PTree, TR:PTree)) => maxInt(Z, maxInt(ptree_max_priority(TL), ptree_max_priority(TR)))
  rule ptree_max_priority(pleaf) => 0
  //
  rule ptree_max_priority(_:PTree) >=Int 0 => true    [smt-lemma]

  syntax Int ::= "ptree_priority" "(" PTree ")"    [function, smtlib(smt_ptree_priority)]
  rule ptree_priority(pnode(_, Z:Int, _, _)) => Z
  rule ptree_priority(pleaf) => 0
  //
  rule ptree_priority(_:PTree) >=Int 0 => true    [smt-lemma]

  syntax Bool ::= "treap" "(" PTree ")"   [function, smtlib(smt_treap)]
  rule treap(pnode(I:Int, Z:Int, TL:PTree, TR:PTree))
    => treap(TL) andBool treap(TR)
       andBool ptree_keys(TL) <IntSet { I } andBool { I } <IntSet ptree_keys(TR)
       andBool Z >=Int ptree_max_priority(TL) andBool Z >=Int ptree_max_priority(TR)
       andBool Z >=Int 0
  rule treap(pleaf) => true
  //
  rule treap(T:PTree) impliesBool ptree_max_priority(T) ==K ptree_priority(T) => true    [smt-lemma]

  syntax Bag ::= "ptree" "(" RawRefVal ")" "(" PTree ")"   [pattern(1)]
  rule
    <objectStore>...
      ptree(objectRef(P:Int, C:ClassType))(pnode(I:Int, Z:Int, TL:PTree, TR:PTree))
    =>
      <object>
        <objectId> P </objectId>
        <objectType> C </objectType>
        <layer>
          <layerClass> C </layerClass>
          <layerEnv>
            String2Id("value")    |-> I :: int
            String2Id("priority") |-> Z :: int
            String2Id("left")     |-> ?PL:RawRefVal :: C
            String2Id("right")    |-> ?PR:RawRefVal :: C
          </layerEnv>
          <layerEnclosingObject> noValue </layerEnclosingObject>
        </layer>
        <layer>
          <layerClass> class String2Id("java.lang.Object") </layerClass>
          <layerEnv> .Map </layerEnv>
          <layerEnclosingObject> noValue </layerEnclosingObject>
        </layer>
      </object>
      ptree(?PL)(TL)
      ptree(?PR)(TR)
    ...</objectStore>
  ensures true
  andBool -2147483648 <=Int I andBool I <=Int 2147483647
  andBool -2147483648 <=Int Z andBool Z <=Int 2147483647
  andBool Z >=Int 0
    [pattern]
  rule <objectStore>... ptree(null)(pleaf) => .Bag ...</objectStore>
    [pattern]

endmodule

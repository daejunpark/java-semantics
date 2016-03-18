// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module RBT-PATTERN
  imports MAP
  imports JAVA-EXEC
  imports INT-SET

  syntax CTree ::= "cnode" "(" Int "," Int "," CTree "," CTree ")" // Red=0, Black=1
                 | "cleaf"

  syntax IntSet ::= "ctree_keys" "(" CTree ")"    [function, smtlib(smt_ctree_keys)]
  rule ctree_keys(cnode(I:Int, _, TL:CTree, TR:CTree)) => { I } U (ctree_keys(TL) U ctree_keys(TR))
  rule ctree_keys(cleaf) => .IntSet

  syntax Int ::= "ctree_height" "(" CTree ")"      [function, smtlib(smt_ctree_height)]
  rule ctree_height(cnode(_, C:Int, TL:CTree, TR:CTree)) => C +Int maxInt(ctree_height(TL), ctree_height(TR))
  rule ctree_height(cleaf) => 0
  //
  rule ctree_height(T:CTree) >=Int 0 => true [smt-lemma]

  syntax Int ::= "ctree_color" "(" CTree ")"      [function, smtlib(smt_ctree_color)]
  rule ctree_color(cnode(_, C:Int, _, _)) => C
  rule ctree_color(cleaf) => 1
  //
  rule ctree_color(T:CTree) ==K 1 orBool ctree_color(T) ==K 0 => true [smt-lemma]
  
  syntax Bool ::= "rbt" "(" CTree ")"             [function, smtlib(smt_rbt)]
  rule rbt(cnode(I:Int, C:Int, TL:CTree, TR:CTree))
    => rbt(TL) andBool rbt(TR)
       andBool ctree_keys(TL) <IntSet { I } andBool { I } <IntSet ctree_keys(TR)
       andBool ctree_height(TL) ==Int ctree_height(TR)
       andBool ( C ==K 1 orBool C ==K 0 )
       andBool (
                 C ==K 1
               orBool
                 (ctree_color(TL) ==K 1 andBool ctree_color(TR) ==K 1)
               )
  rule rbt(cleaf) => true

  syntax Bag ::= "ctree" "(" RawRefVal ")" "(" CTree ")"   [pattern(1)]
  rule
    <objectStore>...
      ctree(objectRef(P:Int, CT:ClassType))(cnode(I:Int, C:Int, TL:CTree, TR:CTree))
    =>
      <object>
        <objectId> P </objectId>
        <objectType> CT </objectType>
        <layer>
          <layerClass> CT </layerClass>
          <layerEnv>
            String2Id("value") |-> I :: int
            String2Id("color") |-> C :: int
            String2Id("left")  |-> ?PL:RawRefVal :: CT
            String2Id("right") |-> ?PR:RawRefVal :: CT
          </layerEnv>
          <layerEnclosingObject> noValue </layerEnclosingObject>
        </layer>
        <layer>
          <layerClass> class String2Id("java.lang.Object") </layerClass>
          <layerEnv> .Map </layerEnv>
          <layerEnclosingObject> noValue </layerEnclosingObject>
        </layer>
      </object>
      ctree(?PL)(TL)
      ctree(?PR)(TR)
    ...</objectStore>
    ensures true
    andBool -2147483648 <=Int I andBool I <=Int 2147483647
    andBool -2147483648 <=Int C andBool C <=Int 2147483647
    [pattern]
  rule <objectStore>... ctree(null)(cleaf) => .Bag ...</objectStore>
    [pattern]

endmodule

require "java-verification.k"

module TREAP-DELETE-SPEC
imports JAVA-VERIFICATION

rule
  <classes> CLASSES:Bag </classes>
  <NumOfClassesToUnfold> 0 </NumOfClassesToUnfold>
  <program> .K </program>
  <globalPhase> ExecutionPhase </globalPhase>
  <store>... .Map => ?_:Map ...</store>
  <busy> .Set </busy>
  <nextLoc> _:Int => ?_:Int </nextLoc>
  <threads>
    <thread>
      <k>
	    (class String2Id(".treap")).String2Id("delete_root"):Id((TP1:RawRefVal)::(class String2Id(".treap")))
      =>
        ?TP2:RawRefVal::(class String2Id(".treap"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    ptree( TP1)(pnode(I1:Int,Z1:Int,L1:PTree,R1:PTree))
  =>
    ptree(?TP2)(?T2:PTree)
  )
    (.Bag => ?_:Bag)
  ...</objectStore>
requires treap(pnode(I1:Int,Z1:Int,L1:PTree,R1:PTree))
  andBool TP1 =/=K null
  andBool -2147483648 <=Int I1 andBool I1 <=Int 2147483647
  andBool -2147483648 <=Int Z1 andBool Z1 <=Int 2147483647
ensures treap(?T2)
  andBool ptree_keys(?T2) ==K ptree_keys(L1) U ptree_keys(R1)
  andBool ptree_max_priority(?T2) ==Int maxInt(ptree_max_priority(L1), ptree_max_priority(R1))

rule
  <classes> CLASSES:Bag </classes>
  <NumOfClassesToUnfold> 0 </NumOfClassesToUnfold>
  <program> .K </program>
  <globalPhase> ExecutionPhase </globalPhase>
  <store>... .Map => ?_:Map ...</store>
  <busy> .Set </busy>
  <nextLoc> _:Int => ?_:Int </nextLoc>
  <threads>
    <thread>
      <k>
	    (class String2Id(".treap")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".treap")))
      =>
        ?TP2:RawRefVal::(class String2Id(".treap"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    ptree( TP1)( T1:PTree)
  =>
    ptree(?TP2)(?T2:PTree)
  )
    (.Bag => ?_:Bag)
  ...</objectStore>
requires treap(T1)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool V inIntSet ptree_keys(T1)
ensures treap(?T2)
  andBool ptree_keys(?T2) ==K (ptree_keys(T1) -IntSet { V })
  andBool ptree_max_priority(?T2) <=Int ptree_max_priority(T1)

rule
  <classes> CLASSES:Bag </classes>
  <NumOfClassesToUnfold> 0 </NumOfClassesToUnfold>
  <program> .K </program>
  <globalPhase> ExecutionPhase </globalPhase>
  <store>... .Map => ?_:Map ...</store>
  <busy> .Set </busy>
  <nextLoc> _:Int => ?_:Int </nextLoc>
  <threads>
    <thread>
      <k>
	    (class String2Id(".treap")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".treap")))
      =>
        ?TP2:RawRefVal::(class String2Id(".treap"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    ptree( TP1)( T1:PTree)
  =>
    ptree(?TP2)(?T2:PTree)
  )
  ...</objectStore>
requires treap(T1)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool (notBool (V inIntSet ptree_keys(T1)))
ensures treap(?T2)
  andBool ptree_keys(?T2) ==K (ptree_keys(T1) -IntSet { V })
  andBool ptree_max_priority(?T2) <=Int ptree_max_priority(T1)

endmodule

require "java-verification.k"

module BST-DELETE-SPEC
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
        (class String2Id(".bst")).String2Id("find_min"):Id((TP:RawRefVal)::(class String2Id(".bst")))
      =>
        ?M:Int::int
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>... tree(TP)(T:Tree) ...</objectStore>
requires TP =/=K null andBool bst(T)
ensures (?M inIntSet tree_keys(T)) andBool ({ ?M } <=IntSet tree_keys(T))
  andBool ?M >=Int -2147483648 andBool ?M <=Int 2147483647

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
	    (class String2Id(".bst")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".bst")))
      =>
        ?TP2:RawRefVal::(class String2Id(".bst"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    tree( TP1)( T1:Tree)
  =>
    tree(?TP2)(?T2:Tree)
  )
    (.Bag => ?_:Bag)
  ...</objectStore>
requires bst(T1)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool V inIntSet tree_keys(T1)
ensures bst(?T2)
  andBool tree_keys(?T2) ==K (tree_keys(T1) -IntSet { V })

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
	    (class String2Id(".bst")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".bst")))
      =>
        ?TP2:RawRefVal::(class String2Id(".bst"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    tree( TP1)( T1:Tree)
  =>
    tree(?TP2)(?T2:Tree)
  )
  ...</objectStore>
requires bst(T1)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool (notBool (V inIntSet tree_keys(T1)))
ensures bst(?T2)
  andBool tree_keys(?T2) ==K (tree_keys(T1) -IntSet { V })

endmodule

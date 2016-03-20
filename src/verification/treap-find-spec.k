require "java-verification.k"

module TREAP-FIND-SPEC
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
        (class String2Id(".treap")).String2Id("find"):Id(V:Int::int, (TP:RawRefVal)::(class String2Id(".treap")))
      =>
        ?B:Bool::bool
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>... ptree(TP)(T:PTree) ...</objectStore>
requires treap(T)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
ensures ?B ==K (V inIntSet ptree_keys(T))

endmodule

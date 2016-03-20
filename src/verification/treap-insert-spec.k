require "java-verification.k"

module TREAP-INSERT-SPEC
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
        (class String2Id(".treap")).String2Id("insert"):Id(V:Int::int, Z:Int::int, (TP1:RawRefVal)::(class String2Id(".treap")))
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
    ptree(?TP2)(pnode(?I2:Int,?Z2:Int,?L2:PTree,?R2:PTree))
  )
  ...</objectStore>
requires treap(T1)
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool -2147483648 <=Int Z andBool Z <=Int 2147483647
  andBool Z >=Int 0
ensures treap(pnode(?I2,?Z2,?L2,?R2))
  andBool ptree_keys(pnode(?I2,?Z2,?L2,?R2)) ==K { V } U ptree_keys(T1)
  andBool ?TP2 =/=K null
  andBool ptree_max_priority(T1) >=Int ptree_max_priority(?L2)
  andBool ptree_max_priority(T1) >=Int ptree_max_priority(?R2)
  andBool -2147483648 <=Int ?I2 andBool ?I2 <=Int 2147483647
  andBool -2147483648 <=Int ?Z2 andBool ?Z2 <=Int 2147483647

endmodule

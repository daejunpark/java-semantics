require "java-verification.k"

module RBT-INSERT-SPEC
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
        (class String2Id(".rbt")).String2Id("color"):Id((TP:RawRefVal)::(class String2Id(".rbt")))
      =>
        ctree_color(T)::int
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>... ctree(TP)(T:CTree) ...</objectStore>
ensures ctree_color(T) ==K 1 orBool ctree_color(T) ==K 0

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
        (class String2Id(".rbt")).String2Id("insert_aux"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        ?TP2:RawRefVal::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    ctree( TP1)(T1:CTree)
  =>
    ctree(?TP2)(cnode(?I2:Int,?C2:Int,?L2:CTree,?R2:CTree))
  )
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
ensures rbt(?L2) andBool rbt(?R2)
  andBool ctree_keys(?L2) <IntSet { ?I2 } andBool { ?I2 } <IntSet ctree_keys(?R2)
  andBool ctree_height(?L2) ==Int ctree_height(?R2)
  andBool ( ?C2 ==K 1 orBool ?C2 ==K 0 )
  andBool (
            ?C2 ==K 1
          orBool
            (
              ( ctree_color(?L2) ==K 1 andBool ctree_color(?R2) ==K 1 )
            orBool
              ( 
                ctree_color(T1) =/=K 1
              andBool
                ( ctree_color(?L2) ==K 1 orBool ctree_color(?R2) ==K 1 )
              )
            )
          )
  andBool ctree_keys(cnode(?I2,?C2,?L2,?R2)) ==K { V } U ctree_keys(T1)
  andBool ctree_height(T1) ==Int ctree_height(cnode(?I2,?C2,?L2,?R2))
  andBool ?TP2 =/=K null


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
        (class String2Id(".rbt")).String2Id("insert"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        ?TP2:RawRefVal::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
  (
    ctree( TP1)( T1:CTree)
  =>
    ctree(?TP2)(?T2:CTree)
  )
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
ensures rbt(?T2)
  andBool ctree_keys(?T2) ==K { V } U ctree_keys(T1)
  andBool ctree_height(T1) <=Int ctree_height(?T2)
  andBool ctree_height(?T2) <=Int ctree_height(T1) +Int 1

endmodule

require "java-verification.k"

module RBT-DELETE-SPEC
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
        (class String2Id(".rbt")).String2Id("find_min"):Id((TP:RawRefVal)::(class String2Id(".rbt")))
      =>
        ?M:Int::int
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>... ctree(TP)(T:CTree) ...</objectStore>
requires TP =/=K null andBool rbt(T)
ensures (?M inIntSet ctree_keys(T)) andBool ({ ?M } <=IntSet ctree_keys(T))
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
        (class String2Id(".rbt")).String2Id("left_delete_fixup"):Id(
            objectRef(FP:Int, class String2Id(".ref"))::(class String2Id(".ref")),
            (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        (?TP2:RawRefVal)::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
    <object>
      <objectId> FP </objectId>
      <objectType> class String2Id(".ref") </objectType>
      <layer>
        <layerClass> class String2Id(".ref") </layerClass>
        <layerEnv>
        (
          String2Id("fixed") |->  F1:Int :: int
        =>
          String2Id("fixed") |-> ?F2:Int :: int
        )
        </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
      <layer>
        <layerClass> class String2Id("java.lang.Object") </layerClass>
        <layerEnv> .Map </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
    </object>
  (
    ctree( TP1)(cnode( I1:Int, C1:Int, L1:CTree,cnode(RI1:Int,RC1:Int,RL1:CTree,RR1:CTree)))
  =>
    ctree(?TP2)(cnode(?I2:Int,?C2:Int,?L2:CTree,?R2:CTree))
  )
  ...</objectStore>
requires F1 =/=K 1
  andBool rbt(L1) andBool rbt(cnode(RI1,RC1,RL1,RR1))
  andBool ctree_keys(L1) <IntSet { I1 } andBool { I1 } <IntSet ctree_keys(cnode(RI1,RC1,RL1,RR1))
  andBool ctree_height(L1) ==Int ctree_height(cnode(RI1,RC1,RL1,RR1)) -Int 1
  andBool ctree_color(L1) ==K 1 andBool ( C1 ==K 1 orBool RC1 ==K 1 )
  andBool ( C1 ==K 1 orBool C1 ==K 0 )
  andBool TP1 =/=K null
  andBool -2147483648 <=Int  I1 andBool  I1 <=Int 2147483647
//andBool -2147483648 <=Int  C1 andBool  C1 <=Int 2147483647
//andBool -2147483648 <=Int RI1 andBool RI1 <=Int 2147483647
//andBool -2147483648 <=Int RC1 andBool RC1 <=Int 2147483647
  andBool ctree_height(L1) <=Int 2147483647 -Int 1 -Int C1
  andBool (
            F1 ==K 1
          orBool
            F1 ==K 0
          )
ensures rbt(cnode(?I2,?C2,?L2,?R2))
  andBool ctree_keys(cnode(?I2,?C2,?L2,?R2)) ==K ctree_keys(cnode(I1,C1,L1,cnode(RI1,RC1,RL1,RR1)))
  andBool (
            ?C2 ==K 1
          orBool
            ?C2 ==K C1
          )
  andBool (
            (
              ?F2 ==K 1
            andBool ctree_height(cnode(?I2,?C2,?L2,?R2)) ==Int ctree_height(L1) +Int C1 +Int 1
            )
          orBool
            (
              ?F2 =/=K 1
            andBool C1 ==K 1
            andBool ?C2 ==K 1
            andBool ctree_height(cnode(?I2,?C2,?L2,?R2)) ==Int ctree_height(L1) +Int C1
            )
          )
  andBool ( C1 =/=K 1 impliesBool ?F2 ==K 1 )
  andBool ?TP2 =/=K null
  andBool (
            ?F2 ==K 1
          orBool
            ?F2 ==K 0
          )
  andBool -2147483648 <=Int ?I2 andBool ?I2 <=Int 2147483647
  andBool -2147483648 <=Int ?C2 andBool ?C2 <=Int 2147483647

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
        (class String2Id(".rbt")).String2Id("right_delete_fixup"):Id(
            objectRef(FP:Int, class String2Id(".ref"))::(class String2Id(".ref")),
            (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        (?TP2:RawRefVal)::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
    <object>
      <objectId> FP </objectId>
      <objectType> class String2Id(".ref") </objectType>
      <layer>
        <layerClass> class String2Id(".ref") </layerClass>
        <layerEnv>
        (
          String2Id("fixed") |->  F1:Int :: int
        =>
          String2Id("fixed") |-> ?F2:Int :: int
        )
        </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
      <layer>
        <layerClass> class String2Id("java.lang.Object") </layerClass>
        <layerEnv> .Map </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
    </object>
  (
    ctree( TP1)(cnode( I1:Int, C1:Int,cnode(LI1:Int,LC1:Int,LL1:CTree,LR1:CTree), R1:CTree))
  =>
    ctree(?TP2)(cnode(?I2:Int,?C2:Int,?L2:CTree,                                 ?R2:CTree))
  )
  ...</objectStore>
requires F1 =/=K 1
  andBool rbt(cnode(LI1,LC1,LL1,LR1)) andBool rbt(R1)
  andBool ctree_keys(cnode(LI1,LC1,LL1,LR1)) <IntSet { I1 } andBool { I1 } <IntSet ctree_keys(R1)
  andBool ctree_height(R1) ==Int ctree_height(cnode(LI1,LC1,LL1,LR1)) -Int 1
  andBool ctree_color(R1) ==K 1 andBool ( C1 ==K 1 orBool LC1 ==K 1 )
  andBool ( C1 ==K 1 orBool C1 ==K 0 )
  andBool TP1 =/=K null
  andBool -2147483648 <=Int  I1 andBool  I1 <=Int 2147483647
//andBool -2147483648 <=Int  C1 andBool  C1 <=Int 2147483647
//andBool -2147483648 <=Int LI1 andBool LI1 <=Int 2147483647
//andBool -2147483648 <=Int LC1 andBool LC1 <=Int 2147483647
  andBool ctree_height(R1) <=Int 2147483647 -Int 1 -Int C1
  andBool (
            F1 ==K 1
          orBool
            F1 ==K 0
          )
ensures rbt(cnode(?I2,?C2,?L2,?R2))
  andBool ctree_keys(cnode(?I2,?C2,?L2,?R2)) ==K ctree_keys(cnode(I1,C1,cnode(LI1,LC1,LL1,LR1),R1))
  andBool (
            ?C2 ==K 1
          orBool
            ?C2 ==K C1
          )
  andBool (
            (
              ?F2 ==K 1
            andBool ctree_height(cnode(?I2,?C2,?L2,?R2)) ==Int ctree_height(R1) +Int C1 +Int 1
            )
          orBool
            (
              ?F2 =/=K 1
            andBool C1 ==K 1
            andBool ?C2 ==K 1
            andBool ctree_height(cnode(?I2,?C2,?L2,?R2)) ==Int ctree_height(R1) +Int C1
            )
          )
  andBool ( C1 =/=K 1 impliesBool ?F2 ==K 1 )
  andBool ?TP2 =/=K null
  andBool (
            ?F2 ==K 1
          orBool
            ?F2 ==K 0
          )
  andBool -2147483648 <=Int ?I2 andBool ?I2 <=Int 2147483647
  andBool -2147483648 <=Int ?C2 andBool ?C2 <=Int 2147483647

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
        (class String2Id(".rbt")).String2Id("delete_aux"):Id(
            objectRef(FP:Int, class String2Id(".ref"))::(class String2Id(".ref")),
            V:Int::int,
            (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        (?TP2:RawRefVal)::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
    <object>
      <objectId> FP </objectId>
      <objectType> class String2Id(".ref") </objectType>
      <layer>
        <layerClass> class String2Id(".ref") </layerClass>
        <layerEnv>
        (
          String2Id("fixed") |->  F1:Int :: int
        =>
          String2Id("fixed") |-> ?F2:Int :: int
        )
        </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
      <layer>
        <layerClass> class String2Id("java.lang.Object") </layerClass>
        <layerEnv> .Map </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
    </object>
  (
    ctree( TP1)( T1:CTree)
  =>
    ctree(?TP2)(?T2:CTree)
  )
    (.Bag => ?_:Bag)
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool (
            F1 ==K 1
          orBool
            F1 ==K 0
          )
  andBool V inIntSet ctree_keys(T1)
ensures rbt(?T2)
  andBool ctree_keys(?T2) ==K (ctree_keys(T1) -IntSet { V })
  andBool (
            ctree_color(?T2) ==K 1
          orBool
            ctree_color(?T2) ==K ctree_color(T1)
          )
  andBool (
            (
              ?F2 ==K 1
            andBool ctree_height(?T2) ==Int ctree_height(T1)
            )
          orBool
            (
              ?F2 =/=K 1
            andBool ctree_height(?T2) ==Int ctree_height(T1) -Int 1
            andBool ctree_color(?T2) ==K 1
            )
          )
  andBool (
            ?F2 ==K 1
          orBool
            ?F2 ==K 0
          )

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
        (class String2Id(".rbt")).String2Id("delete_aux"):Id(
            objectRef(FP:Int, class String2Id(".ref"))::(class String2Id(".ref")),
            V:Int::int,
            (TP1:RawRefVal)::(class String2Id(".rbt")))
      =>
        (?TP2:RawRefVal)::(class String2Id(".rbt"))
      ...</k>
      <holds> .Map </holds>
  ...</thread>
  </threads>
  <objectStore>...
    <object>
      <objectId> FP </objectId>
      <objectType> class String2Id(".ref") </objectType>
      <layer>
        <layerClass> class String2Id(".ref") </layerClass>
        <layerEnv>
        (
          String2Id("fixed") |->  F1:Int :: int
        =>
          String2Id("fixed") |-> ?F2:Int :: int
        )
        </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
      <layer>
        <layerClass> class String2Id("java.lang.Object") </layerClass>
        <layerEnv> .Map </layerEnv>
        <layerEnclosingObject> noValue </layerEnclosingObject>
      </layer>
    </object>
  (
    ctree( TP1)( T1:CTree)
  =>
    ctree(?TP2)(?T2:CTree)
  )
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool (
            F1 ==K 1
          orBool
            F1 ==K 0
          )
  andBool (notBool (V inIntSet ctree_keys(T1)))
ensures rbt(?T2)
  andBool ctree_keys(?T2) ==K (ctree_keys(T1) -IntSet { V })
  andBool (
            ctree_color(?T2) ==K 1
          orBool
            ctree_color(?T2) ==K ctree_color(T1)
          )
  andBool (
            (
              ?F2 ==K 1
            andBool ctree_height(?T2) ==Int ctree_height(T1)
            )
          orBool
            (
              ?F2 =/=K 1
            andBool ctree_height(?T2) ==Int ctree_height(T1) -Int 1
            andBool ctree_color(?T2) ==K 1
            )
          )
  andBool (
            ?F2 ==K 1
          orBool
            ?F2 ==K 0
          )

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
	    (class String2Id(".rbt")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".rbt")))
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
    (.Bag => ?_:Bag)
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool V inIntSet ctree_keys(T1)
ensures rbt(?T2)
  andBool ctree_keys(?T2) ==K (ctree_keys(T1) -IntSet { V })
  andBool ctree_height(T1) -Int 1 <=Int ctree_height(?T2)
  andBool ctree_height(?T2) <=Int ctree_height(T1)

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
	    (class String2Id(".rbt")).String2Id("delete"):Id(V:Int::int, (TP1:RawRefVal)::(class String2Id(".rbt")))
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
    (.Bag => ?_:Bag)
  ...</objectStore>
requires rbt(T1)
  andBool ctree_height(T1) <=Int 2147483647
  andBool -2147483648 <=Int V andBool V <=Int 2147483647
  andBool (notBool (V inIntSet ctree_keys(T1)))
ensures rbt(?T2)
  andBool ctree_keys(?T2) ==K (ctree_keys(T1) -IntSet { V })
  andBool ctree_height(T1) -Int 1 <=Int ctree_height(?T2)
  andBool ctree_height(?T2) <=Int ctree_height(T1)

endmodule

module API-THREADS
    imports CORE-SORTS
    imports METHOD-INVOKE-REST  //for invokeImpl
    imports VAR-LOOKUP          //for typedLookup

/*@Java API related to threads and locks. Just the core part.*/

//@ \subsection{Method Thread.start()}
rule [thread-start]:
    <thread>
      <k>
        invokeImpl(
          methodRef(sig(MethodName:Id, _), Class:ClassType),
          objectRef(OL:Int,_)::_,
          [TId:Int :: _]
        ) => nothing::void
        ...
      </k>
      ...
    </thread>

    (. =>
      <thread>
        <k>
          //typedLookup(OL).runnable.run()
          'Field(
            cast(
              class String2Id("java.lang.Thread"),
              typedLookup(OL)
            ),,
            String2Id("runnable")
          )
          .String2Id("run"):Id (.TypedVals) ;
        </k>
        <tid> TId </tid>
        ...
      </thread>
    )
when
    Class ==K class String2Id("java.lang.Thread") andBool Id2String(MethodName) ==String "startImpl"

//@ \subsection{Synchronized statement}
/*this context is added because strict(1) in syntax definition of synchronized stmt does not apply
 because second argument Block does not conform to syntax (has KListWrap). Remove later. */
context synchronized (HOLE) _:K

rule [Synchronized-first-time]:
    <k>
          synchronized (objectRef(OId:Int,_)::_) Block:K
          => try Block .CatchClauses finally releaseLock(OId)
          ...
    </k>
    <holds>... (.Map => OId |-> 1) ...</holds>
    <busy> Busy:Set (.Set => SetItem(OId)) </busy>
when
    notBool (OId in Busy)
        [transition-threading, transition-sync]

rule [Synchronized-nested]:
    <k>
            synchronized (objectRef(OId:Int,_)::_) Block:K
            => try Block .CatchClauses finally releaseLock(OId)
      ...
    </k>
    <holds>... OId |-> (Level:Int => Level +Int 1) ...</holds>
        [transition-threading, transition-sync]

rule [Synchronized-on-null]:
    synchronized (null::_) _:K => throw new classNullPointerException(null::classString);

/*@Release one level of lock for the given object.*/
syntax KItem ::=  releaseLock ( Int )

rule [releaseLock]:
    <k>
      releaseLock(OL:Int) => .
      ...
    </k>
    <holds>... OL |-> (Level:Int => Level -Int 1) ...</holds>
        [transition-threading]

/*
K performance evaluation with the rule below active and commented:
  helloWorld vanilla: 22.5s
  helloWorld rule commented: 22.15s
  22_array_separated 42 tests, vanilla: 336s
  22_array_separated 42 tests, rule commented: 335s

  Conclusion: the rule below have no impact on performance.
*/

rule [monitor-completely-released]:
    <holds> M:Map => removeMapItemsByValue(M,0) </holds>
    <busy> S:Set => S -Set keys(M -Map removeMapItemsByValue(M,0)) </busy>
    when 0 in values(M)

//@ \subsection{Thread.join()}

rule [thread-join]:
    <k>
      invokeImpl(
        methodRef(sig(MethodName:Id, _), Class:ClassType), _,
        [TId:Int :: _]
      ) => nothing::void
      ...
    </k>
    <interrupted> false </interrupted>
    <terminated>... SetItem(TId) ...</terminated>
when
    Class ==K class String2Id("java.lang.Thread") andBool Id2String(MethodName) ==String "joinImpl"
        [transition-threading, transition-sync]

rule [thread-join-interrupted]:
    <k>
      invokeImpl(
        methodRef(sig(MethodName:Id, _), Class:ClassType), _,
        [TId:Int :: _]
      )
      => throw new class String2Id("java.lang.InterruptedException") (null::classString);
      ...
    </k>
    <interrupted> true => false </interrupted>
when
    Class ==K class String2Id("java.lang.Thread") andBool Id2String(MethodName) ==String "joinImpl"
        [transition-threading, transition-sync]

//@ \subsection{Object.wait()}

rule [object-wait-notify-notifyAll-without-sync]:
    <k>
      objectRef(OL:Int,_)::_ . methodRef(sig(MethodName:Id, _), Class:ClassType) (.TypedVals)
      => throw new class String2Id("java.lang.IllegalMonitorStateException") (null::classString);
      ...
    </k>
    <holds> Holds:Map </holds>
when
            Class ==K classObject
    andBool (
             Id2String(MethodName) ==String "wait"
      orBool Id2String(MethodName) ==String "notify"
      orBool Id2String(MethodName) ==String "notifyAll"
    )
    andBool notBool OL in keys(Holds)

/*@Second part of a wait. Waiting was already registered to <waitingThreads>.
When the record in <waitingThreads> will be deleted, waiting itself shall end.
*/
syntax KItem ::=  waitImpl (
                Int //Monitor object location
              )

rule [waitImpl-interrupted]:
    <k>
      waitImpl(OL:Int) => throw new class String2Id("java.lang.InterruptedException") (null::classString);
      ...
    </k>
    <tid> TId:Int </tid>
    <busy> Busy:Set (.Set => SetItem(OL)) </busy>
    <interrupted> true => false </interrupted>
when
      notBool OL in Busy
        [transition-threading, transition-sync]

//@ \subsection{Object.notify(), Object.notifyAll()}

/*@Implementation of Object.notify(), extracted here to avoid rule superfluousness*/
syntax KItem ::=  notifyImpl (
                Int //store key of the monitor object
              )
//todo how to realise non-determinism: remove an arbitrary item with that value
rule [notifyImpl-someone-waiting]:
    <k>
      notifyImpl(OL:Int) => nothing::void
      ...
    </k>
    <waitingThreads> WT:Map => removeOneMapItemByValue(WT,OL) </waitingThreads>
when OL in values(WT)
        [transition-threading]

rule [notifyImpl-no-one-waiting]:
    <k>
      notifyImpl(OL:Int) => nothing::void
      ...
    </k>
    <waitingThreads> WT:Map </waitingThreads>
when notBool OL in values(WT)
        [transition-threading]

rule [object-notifyAll]:
    <k>
      objectRef(OL:Int,_)::_ . methodRef(sig(MethodName:Id, _), Class:ClassType) (.TypedVals)
      => objectNotifyAllImpl(OL)
      ...
    </k>
    <holds>... OL |-> HoldLevel:Int ...</holds>
when
            Class ==K classObject
    andBool Id2String(MethodName) ==String "notifyAll"
    andBool HoldLevel >=Int 1

/*@Implementation of Object.notifyAll(), extracted here to avoid rule superfluousness*/
syntax KItem ::=  objectNotifyAllImpl (
                Int //store key of the monitor object
              )
//notifyAll has no non-determinism: it notifies all threads atomicly
rule [objectNotifyAllImpl]:
    <k>
      objectNotifyAllImpl(OL:Int) => nothing::void
      ...
    </k>
    <waitingThreads> WT:Map => removeMapItemsByValue(WT,OL) </waitingThreads>
        [transition-threading]

//@ \subsection{Thread.interrupt()}

rule [thread-interrupt]:
    <thread>
      <k>
        invokeImpl(
          methodRef(sig(MethodName:Id, _), Class:ClassType),
          objectRef(OL:Int,_)::_,
          [TId:Int :: _]
        ) => nothing::void
        ...
      </k>
      ...
    </thread>

    <thread>
      <tid> TId </tid>
      <interrupted> _ => true </interrupted>
      ...
    </thread>
when
    Class ==K class String2Id("java.lang.Thread") andBool Id2String(MethodName) ==String "interruptImpl"
        [transition-threading, transition-sync]

rule [thread-interrupt-ended-thread]:
    <k>
      invokeImpl(
        methodRef(sig(MethodName:Id, _), Class:ClassType),
        objectRef(OL:Int,_)::_,
        [TId:Int :: _]
      ) => nothing::void
      ...
    </k>
    <terminated>... SetItem(TId) ...</terminated>
when
    Class ==K class String2Id("java.lang.Thread") andBool Id2String(MethodName) ==String "interruptImpl"
        [transition-threading, transition-sync]

//@ \subsection{Thread termination}

rule [ThreadTermination]:
    ( <thread>
        <k> .K </k>
        <holds> H:Map </holds>
        <tid> TId:Int </tid>
        ...
      </thread>
    => .)
    <busy> Busy:Set => Busy -Set keys(H) </busy>
    <terminated>... .Set => SetItem(TId) ...</terminated>
    <globalPhase> ExecutionPhase </globalPhase>
    <dissolveEmptyK> false </dissolveEmptyK>

//@ \subsection{Debug aids}

/*@ Dissolve all cells except <out> for the purpose of model checking. We will avoid duplicates caused by the same
    <out> but different order of content in other cells.*/
rule [DissolveAllExceptOut]:
    <T>
      <out> Out:List </out>
      <threads> .Bag </threads>
      <globalPhase> ExecutionPhase </globalPhase>
      <dissolveAllExceptOut> true </dissolveAllExceptOut>
      ...
    </T>
    => <T> <out> Out </out> </T>


//@ \subsection{Methods wait() and notify()}

/*@
When \verb|object.wait()| is called the method call expression is replaced by \verb|waitImpl()|
-- an auxiliary function that is used later to exit from the waiting state.
The id of the current thread (\verb|TId|) has to be registered in the set inside \cellref[]{waitingThreads}.
  The cell \cellref[]{holds} attached to each thread stores the number of times the current thread
  acquired the lock on each object. Here we use it to make sure that the current thread acquired the lock at least once
  (see the side condition). Otherwise calling the method \verb|wait()| is illegal and we have to throw an exception, according
  to Java API. The exceptional case is covered by other rules. Another cell matched here is \cellref[]{busy}. It stores
  the set of objects that serve as synchronization monitors -- arguments of blocks \verb|synchronized|. When
  an object enters the waiting state it have to release the ownership of this monitor, this is reflected by deleting
  the entry \verb|OL| from the set. In this rule the cell \cellref[]{thread} is used solely for clarity, to separate
  the cells that are attached to a thread from global cells. In fact, if we would delete \cellref[]{thread} here and
  keep just what is inside, the semantics of the rule would not change. This is because configuration abstraction
  mechanism of \K would infer the surrounding context for each of \cellref[]{k} \cellref[]{tid} and \cellref[]{holds}.
  It would know to match them under the same \cellref[]{thread}, even if there are multiple \cellref[]{thread} cells.
*/
rule [object-wait]:
    <thread> //added just for clarity, to illustrate the distinctive context of <holds> and <busy>
      <k>
        objectRef(OId:Int, _)::_ . methodRef(sig(Method:Id, _), Class:ClassType) (.TypedVals)
        => waitImpl(OId)
        ...
      </k>
      <tid> TId:Int </tid>
      <holds>... OId |-> HoldLevel:Int ...</holds>
      ...
    </thread>
    <busy>... (SetItem(OId) => .Set) ...</busy>
    <waitingThreads>... (.Map => TId |-> OId ) ...</waitingThreads>
when
            Class ==K classObject
    andBool Id2String(Method) ==String "wait"
    andBool HoldLevel >=Int 1
        [transition-threading]

/*@
When another thread calls \verb|notify()| we have to make sure that the thread holds the monitor on the target object
  (the side condition). Otherwise we have to throw an exception. The actual logic of \verb|notify()| is delegated
  to \verb|notifyImpl()|, in order to avoid duplication. The construct \verb|notifyImpl()| requires two rules for two
  cases -- the case when there is at least one thread waiting on the target object, and the case when there is no one.
*/
rule [object-notify]:
    <k>
      objectRef(OId:Int, _)::_ . methodRef(sig(Method:Id, _), Class:ClassType) (.TypedVals)
      => notifyImpl(OId)
      ...
    </k>
    <holds>... OId |-> HoldLevel:Int ...</holds>
when
            Class ==K classObject
    andBool Id2String(Method) ==String "notify"
    andBool HoldLevel >=Int 1

/*@
At this stage the rule for \verb|waitImpl()| could match. The rule checks in its side conditions that the current
  thread id \verb|TId| is not among the waiting threads anymore. It also checks that the target object, represented by
  \verb|OId| is not busy. This is required because the thread exiting from waiting state have to reacquire the monitor
  on the target object. Finally, the rule have to make sure that the thread was not interrupted while it was waiting.
  Otherwise another rule will match and will throw the appropriate exception.
*/
rule [waitImpl-main]:
    <k> waitImpl(OId:Int) => nothing::void ...</k>
    <tid> TId:Int </tid>
    <busy> Busy:Set (.Set => SetItem(OId)) </busy>
    <interrupted> false </interrupted>
    <waitingThreads> WT:Map </waitingThreads>
when
            (notBool TId in keys(WT))
    andBool (notBool OId in Busy)
        [transition-threading, transition-sync]

endmodule

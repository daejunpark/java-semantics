module ELABORATION-STATEMENTS
    imports CORE-SORTS
    imports ELABORATION-CORE
    imports ELABORATION-METHOD-INVOKE //for lookupMethod
    imports PROCESS-LOCAL-CLASSES //for localClassGetExtraArgs

//@ Elaboration of 'KListWrap, 'Block, 'For or 'Catch - nodes that may contain variable declarations.

//K bug: support for KListWrap. This rule was replaced by a special section for elaboration of KListWrap.
// See other K-bug-s.
/* 'KListWrap nodes need to be elaborated left-to-right. Required when direct child elements might contain variable
declarations.
*/
//rule customElabHeating('KListWrap, HeadKs:KList,, K:K) => isElabKList(HeadKs)

syntax KItem ::= isVarDecHolderLabel ( KLabel )                 [function]
rule isVarDecHolderLabel('Block) => true
rule isVarDecHolderLabel('For) => true
rule isVarDecHolderLabel('Catch) => true
rule isVarDecHolderLabel(_) => false [owise]

/*@ In addition to what defaul elab heating does, when we heat the first argument of 'Block, 'For of 'Catch
we need to save a copy of elaboration environment - e.g. the last entry of <elabEnv> <localTypes>.
This is because these statements are blocks that might declare local variables. Empty Expressions are KResult and
therefore ElabKResult, but we should still copy the env because removeLastElabEnv removes indifferently.
*/
rule [elab-Block-For-Catch-heat-FirstSubterm]:
    <k> elab(KL:KLabel(K:K,, Ks:KList)) => elab(K) ~> elab(KL(CHOLE,, Ks:KList)) ...</k>
    <elabEnv> (.List => ListItem(ElabEnvLI)) ListItem(ElabEnvLI:K) ...</elabEnv>
    <localTypes> (.List => ListItem(LocalTypesLI)) ListItem(LocalTypesLI:K) ...</localTypes>
when
    isVarDecHolderLabel(KL) ==K true andBool ((notBool isElabKResult(K)) orBool K ==K .Exps)

//Seqstrict starting from 2-nd argument.
//rule [customElabHeating-For-next-children]:
//    customElabHeating('For, [HeadKs:KList,, KPrec:K,, KHole:K]) => isElabKList([HeadKs,,KPrec])
rule   ( . => elab(Arg2) ) ~> elab('For(Arg1:ElabKResult,,(Arg2:K => CHOLE),,_,,_))
when notBool isElabKResult(Arg2) ==K true

rule   ( . => elab(Arg3) ) ~> elab('For(Arg1:ElabKResult,,Arg2:ElabKResult,,(Arg3:K => CHOLE),,_))
when notBool isElabKResult(Arg3) ==K true

rule   ( . => elab(Arg4) ) ~> elab('For(Arg1:ElabKResult,,Arg2:ElabKResult,,Arg3:ElabKResult,,(Arg4:K => CHOLE)))
when notBool isElabKResult(Arg4) ==K true

//Seqstrict starting from 2-nd argument.
//rule [customElabHeating-For-next-children]:
//    customElabHeating('Catch, [K1:K,, KHole:K]) => isElabKResult(K1)
rule   ( . => elab(Arg2) ) ~> elab('Catch(Arg1:ElabKResult,,(Arg2:K => CHOLE)))
when notBool isElabKResult(Arg2) ==K true


rule [elabEnd-Block-For-Catch]:
    elabEnd(KL:KLabel(ElabResL:KList)) => removeLastElabEnv ~> elabRes(KL(ElabResL))
when
    isVarDecHolderLabel(KL) ==K true

//@ Local var declarations desugaring

rule [elab-LocalVarDecStm-desugar]:
    elab('LocalVarDec(Ks:KList)
      => 'LocalVarDecStm('LocalVarDec(Ks))
    )                                                   [structural]

//@ Resolve the local var type, required to register the var in <elabEnv>
context elab('LocalVarDecStm('LocalVarDec(_:K,, HOLE,, _:K)))
//todo Problem: BlockStmList is cons list, so the result is not a valid list either,
//can use a wrapper around and say that the wrapper is a BlockStmt, heavyweight.
rule [elab-LocalVarDec-multi-desugar]:
    elab('LocalVarDecStm('LocalVarDec(K:K,, T:Type,, 'VarDecList(Var1:K,, 'VarDecList(Var2:K,, VarDecs:K))))
      => 'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, 'VarDecList(Var1,, .VarDecList))),,
            'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, 'VarDecList(Var2,, VarDecs))),, .BlockStmList))
    )                                                   [structural]

rule [elab-LocalVarDec-with-init-desugar]:
    elab('LocalVarDecStm('LocalVarDec(K:K,, T:Type,, 'VarDecList('VarDec(X:Id,,InitExp:K),, .VarDecList)))
    => 'BlockStmList('LocalVarDecStm('LocalVarDec(K,, T,, 'VarDecList('VarDec(X:Id),, .VarDecList))),,
           'BlockStmList('ExprStm('Assign('ExprName(X),, InitExp)),, .BlockStmList))
    )
when
    getKLabel(InitExp) =/=KLabel 'ArrayInit             [structural]

rule [elab-LocalVarDec]:
    <k>
      elab('LocalVarDecStm('LocalVarDec(K:K,, T:Type,, 'VarDecList('VarDec(X:Id),, .VarDecList))))
      => elabRes('LocalVarDecStm('LocalVarDec(K,, T,, 'VarDecList('VarDec(X),, .VarDecList))))
      ...
    </k>
    <elabEnv> ListItem(mapWrap((.Map => X |-> T) _)) ...</elabEnv>

//@\subsection{Elaboration of SuperConstrInv, QSuperConstrInv, AltConstrInv}

// 'SuperConstrInv( _:K,,  Args)
//@ Desugaring unqualified superclass constructor invocation into a qualified one
rule [elab-SuperConstrInv-desugar]:
    <k>
      elab(
        'SuperConstrInv(K:K,, Args:K)
        =>  'QSuperConstrInv(
              #if CT ==K instanceCT
                #then findQualifierOfType(EnclosingClass, BaseEnclosingClass)
                #else noValue
              #fi,,
              K,,
              Args
            )
      )
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <class>
      <classType> Class </classType>
      <extends> BaseClass:ClassType </extends>
      <enclosingClass> EnclosingClass:ClassType </enclosingClass>
      ...
    </class>
    <class>
      <classType> BaseClass </classType>
      <enclosingClass> BaseEnclosingClass:ClassType </enclosingClass>
      <classContextType> CT:ContextType </classContextType>
      ...
    </class>

rule customElabEnd('QSuperConstrInv) => true

rule [elabEnd-QSuperConstrInv-local-augment-arguments]:
    <k>
      (. => localClassGetExtraArgs(BaseClass))
      ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, Args))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <classType> Class </classType>
    <extends> BaseClass:ClassType </extends>

//@ QSuperConstrInv lookup is always unqualified
rule [elabEnd-QSuperConstrInv-to-lookupMethod]:
    <k>
      ( elabRes(ExtraArgs:Exps)
        => lookupMethod(BaseClass, true, getConsName(BaseClass), appendExps(Args,ExtraArgs))
      )
      ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, Args))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>
    <classType> Class </classType>
    <extends> BaseClass:ClassType </extends>

rule [elabEnd-QSuperConstrInv]:
    methodLookupResult(_, ExpectedArgExps:Exps, instanceCT)
    ~> elabEnd('QSuperConstrInv(Qual:K,, Arg2:K,, _))
    => elabRes('QSuperConstrInv(Qual,, Arg2,, ExpectedArgExps ))

rule customElabEnd('AltConstrInv) => true

rule [elabEnd-AltConstrInv-local-augment-arguments]:
    <k>
      (. => localClassGetExtraArgs(Class))
      ~> elabEnd('AltConstrInv(Arg1:K,, Args))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>

//@ AltConstrInv lookup is always unqualified
rule [elabEnd-AltConstrInv-to-lookupMethod]:
    <k>
      ( elabRes(ExtraArgs:Exps)
        => lookupMethod(Class, true, getConsName(Class), appendExps(Args,ExtraArgs))
      )
      ~> elabEnd('AltConstrInv(Arg1:K,, Args))
      ...
    </k>
    <crntClass> Class:ClassType </crntClass>

rule [elab-AltConstrInv]:
    methodLookupResult(_, ExpectedArgExps:Exps, instanceCT)
    ~> elabEnd('AltConstrInv(Arg1:K,, _))
    => elabRes('AltConstrInv(Arg1:K,, ExpectedArgExps))

endmodule

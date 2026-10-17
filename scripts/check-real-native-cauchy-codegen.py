#!/usr/bin/env python3
"""Pinned-C native limit: actual Program callbacks, sharing and continuation.

Native executeAt and the already proved local normalizer are named boundaries
checked for exact resource inputs. Kernel callbacks are opaque compact-interface
inputs: their hidden captures are NOT certified. Prop reindexing/uniformity is
NOT observed. No universal cost/physical-memory theorem is claimed.
Continuation interpretation uses the all-shared allocation branch; in-place
reference-counting/allocator correctness is outside this bounded test.
"""
from pathlib import Path
import re
import runpy
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
base = runpy.run_path(str(ROOT / "scripts/check-real-addition-codegen.py"))
old = runpy.run_path(str(ROOT / "scripts/check-real-family-transport-codegen.py"))
Value, Analysis, PREFIX = base["Value"], base["Analysis"], base["PREFIX"]
tag, require, mutate = old["tag"], old["require"], old["mutate"]
N, R, H, C = (PREFIX+x+"_" for x in ("RelationalRealNativeCauchy", "RelationalRealAddition", "HeterogeneousRealRuntime", "ConstitutiveRuntime"))
PRODUCE, NEXT, LIVE, SERVICE, OBSERVE = (N+x for x in ("produceNativeLimit", "nativeNext", "nativeLiveStep___redArg", "nativeEnvironment", "observeLimit___redArg"))
UNIQUE_MEDIATE = N+"mediateNative"
UNIQUE_TRACE = N+"produceNativeUniquenessTrace"
UNIQUE_PROJECT = N+"NativeUniquenessTrace_toNumerical"
UNIQUE_FUTURE = N+"nativeNumericalFutures___lam__0"
UNIQUE = N+"nativeUnique"
EXEC, ENV, CODE, STEP_NEXT = R+"executeAt", R+"environment", H+"Step_code___redArg", H+"Step_next___redArg"
NORMAL, EXECUTOR, JOURNAL = N+"nativeNormalized___redArg", C+"execute___redArg", C+"ExecutedRequest_completedJournal___redArg"
TRACE = N+"nativeNormalizationTrace___redArg"
SOURCE_CHARGE = PREFIX+"LocalGrouping_sourceCharge"
TRANSPORT = "lp_relational_x2dperimeter_ConstitutiveSearch_Grouping_AcceptanceAction_transport___redArg"
TERMS, KERNELS, MOD, MONO, LAW, BANK, KSTEP, ANSWER = ("l_native_"+x for x in ("terms", "kernels", "modulus", "monotone", "cauchy", "bank", "kernel_step", "kernel_answer"))
UNIQUE_TERMS, UNIQUE_MODULUS, UNIQUE_BANK = (
    "l_native_unique_terms", "l_native_unique_modulus", "l_native_unique_bank")
UNIQUE_FIRST_RATE, UNIQUE_SECOND_RATE = "l_native_unique_first_rate", "l_native_unique_second_rate"
UNIQUE_FIRST_LAW, UNIQUE_SECOND_LAW = "l_native_unique_first_law", "l_native_unique_second_law"
UNIQUE_SYM, UNIQUE_COMPOSE = PREFIX+"Near_symm___redArg", PREFIX+"Near_compose___redArg"


def family():
    # kernelExact is Prop, but monotonicity/Cauchy have positive Type outputs.
    return Value(fields={0:Value(function=TERMS), 1:Value(function=KERNELS), 2:Value(function=MOD), 3:Value(function=MONO), 4:Value(function=LAW)})


def bank():
    return Value(function=BANK)


def source_execution():
    return Value(tags=frozenset({"source-execution"}), fields={0:tag("source-phases"), 1:tag("owned-diagonal")})


def charge():
    return Value(tags=frozenset({"normalized-charge"}), fields={0:tag("native-code"), 1:tag("received-near"), 2:tag("native-code")})


def production():
    return Value(fields={0:source_execution(), 1:Value(tags=frozenset({"grouping-execution"}), fields={0:tag("grouping-phases"), 1:Value(fields={0:source_execution(), 1:charge()})})})


def archive():
    return Value(fields={0:bank(), 1:tag("current-journal"), 2:tag("prior-history"), 3:Value(number=0)})


class NativeAnalysis(Analysis):
    def __init__(self, *args, watched="", unfold_normalizer=False, **kwargs):
        super().__init__(*args, target="", capture=True, **kwargs)
        self.watched = watched
        self.unfold_normalizer = unfold_normalizer

    def invoke(self, closure, arguments):
        if closure.function is None:
            raise ValueError("Native Program callback is not executable")
        return self.run(closure.function, [closure.fields[i] for i in range(closure.fixed)] + arguments)

    def global_value(self, name):
        literal=N+"nativeNormalizationTrace___redArg___closed__0"
        if name in (literal,literal+"_value"):
            if "((size_t)(0) << 1) | 1" not in self.functions[literal+"_value"]:
                raise ValueError("Pinned local source-state literal changed")
            return Value(fields={0:Value(number=0)})
        return super().global_value(name)

    def run(self, name, args):
        count = int(name == self.watched)
        if name in (MOD, TERMS, BANK):
            wanted, result = {MOD:("p","diagonal-index"), TERMS:("diagonal-index","native-real"), BANK:("diagonal-index","current-native-archive")}[name]
            require(args[0],wanted,"Native generator lost requested index/precision")
            return tag(result),count,count
        if name == ENV:
            require(args[2],"native-real","Native environment lost term")
            return tag("native-environment"),count,count
        if name == EXEC:
            for slot,wanted in ((2,"native-real"),(3,"current-native-archive"),(4,"p")):
                require(args[slot],wanted,"Native execution lost received context/precision")
            return tag("owned-diagonal"),count,count
        if name in (R+"executeReal", R+"readout"):
            raise ValueError("Native route substituted canonical readout/execution")
        if name == CODE:
            require(args[-1],"owned-diagonal","Native code does not read owned Step")
            return tag("native-code"),count,count
        if name == STEP_NEXT:
            for slot,wanted in ((0,"native-environment"),(1,"current-native-archive"),(2,"p"),(3,"owned-diagonal")):
                require(args[slot],wanted,"Native continuation lost owned Step/archive")
            return tag("native-successor"),count,count
        if name == NORMAL and not self.unfold_normalizer:
            if args[-1] != source_execution():
                raise ValueError("Native grouping did not consume exact source execution")
            return charge(),count,count
        if name == TRACE:
            if args[-1] != source_execution():
                raise ValueError("Native normalizer trace lost exact source")
            return tag("native-normalization-trace"),count,count
        if name == SOURCE_CHARGE:
            specification=args[0]
            code,lo,hi=self.invoke(specification.fields[1],[Value(number=0)])
            near,a,b=self.invoke(specification.fields[3],[Value(number=0)])
            require(code,"native-code","Native source charge lost exact Step code")
            require(near,"received-near","Native source charge lost native Cauchy law")
            return Value(fields={0:code,1:near}),lo+a+count,hi+b+count
        if name == TRANSPORT:
            specification=args[0].fields[0]
            require(args[2],"native-normalization-trace","Native transport lost executed normalizer")
            require(args[3].fields[0],"native-code","Native grouping charge substituted code")
            require(args[3].fields[1],"received-near","Native grouping charge substituted Near")
            require(specification.fields[2],"native-code","Native target was externally prescribed")
            return charge(),count,count
        if name == JOURNAL:
            phase = "source" if args[0].fields[2].function == N+"nativeSourceProgram___lam__2" else "grouping"
            require(args[1],"current-journal" if phase == "source" else "after-source-journal","Native program reset source/grouping journal")
            return tag("after-"+phase+"-journal"),count,count
        if name == EXECUTOR:
            program = args[0]
            phase = "source" if program.fields[2].function == N+"nativeSourceProgram___lam__2" else "grouping"
            require(args[3],"current-journal" if phase == "source" else "after-source-journal","Native program reset source/grouping journal")
            request=Value(number=0)
            received,lo,hi=self.invoke(program.fields[1],[request])
            searched,a,b=self.invoke(program.fields[2],[request,received]);lo+=a;hi+=b
            acted,a,b=self.invoke(program.fields[3],[request,searched]);lo+=a;hi+=b
            accepted,a,b=self.invoke(program.fields[4],[request,searched,acted]);lo+=a;hi+=b
            authorized,a,b=self.invoke(program.fields[5],[request,searched,acted,accepted]);lo+=a;hi+=b
            decomposed,a,b=self.invoke(program.fields[6],[request,searched,acted,accepted,authorized]);lo+=a;hi+=b
            continued,a,b=self.invoke(program.fields[7],[request,searched,acted,accepted,authorized,decomposed]);lo+=a;hi+=b
            stored,a,b=self.invoke(program.fields[8],[request,searched,acted,accepted,authorized,decomposed,continued]);lo+=a;hi+=b
            for callback,values in ((9,[request,searched,acted]),(10,[request,searched,acted,stored])):
                code,a,b=self.invoke(program.fields[callback],values);lo+=a;hi+=b
                require(code,"native-code","Native action/store did not share target code")
            if phase == "source":
                require(stored,"owned-diagonal","Native source Step was discarded")
            elif stored != Value(fields={0:source_execution(),1:charge()}):
                raise ValueError("Native grouping store lost source/action/target sharing")
            return Value(tags=frozenset({phase+"-execution"}),fields={0:tag(phase+"-phases"),1:stored}),lo+count,hi+count
        if name == "l_List_appendTR___redArg":
            require(args[0],"prior-history","Native retention reset chronological history")
            return Value(tags=frozenset({"extended-history"}),fields={0:args[0],1:args[1]}),count,count
        if name == C+"Journal_root":
            return tag("initial-journal"),count,count
        if name == KERNELS:
            require(args[0],"diagonal-index","Native live kernel lost modulus index")
            env=Value(fields={0:tag("kernel-read"),1:Value(function=KSTEP),2:Value(function=ANSWER)})
            return Value(fields={0:env,1:tag("projected-initial-memory")}),count,count
        if name == KSTEP:
            require(args[0],"projected-initial-memory","Native live step lost projected memory")
            require(args[1],"p","Native live step changed precision")
            return Value(fields={0:tag("kernel-next"),1:tag("kernel-event")}),count,count
        if name == ANSWER:
            require(args[0],"kernel-event","Native live answer lost kernel event")
            return tag("live-code"),count,count
        if name == MONO:
            for value,wanted in zip(args,("coarse","p","hs")):
                require(value,wanted,"Native convergence lost monotone precision")
            return tag("diagonal-extension"),count,count
        if name == LAW:
            if self.unfold_normalizer:
                expected=("p","diagonal-index","diagonal-index","p","p","current-native-archive",
                          "current-native-archive","owned-diagonal","owned-diagonal")
                for value,wanted in zip(args,expected):
                    require(value,wanted,"Native normalizer Cauchy lost exact owned Step")
                return tag("received-near"),count,count
            expected=("coarse","n","diagonal-index","r","p","term-archive","current-native-archive","received-term","owned-diagonal","hn","diagonal-extension","hr","hs")
            for value,wanted in zip(args,expected):
                require(value,wanted,"Native convergence lost received term/owned diagonal")
            if len(args) != len(expected):
                raise ValueError("Native Cauchy callback shape changed")
            return tag("exact-cauchy-near"),count,count
        value,lo,hi=super().run(name,args)
        return value,lo+count,hi+count


def run(functions,params,entry,args,watched="",expected=0,unfold_normalizer=False):
    value,lo,hi=NativeAnalysis(functions,params,base["shared"]["reachable"],watched=watched,unfold_normalizer=unfold_normalizer).run(entry,args)
    if (lo,hi)!=(expected,expected):
        raise ValueError(f"Native multiplicity {watched}: expected {expected}, got [{lo},{hi}]")
    return value


def uniqueness_family():
    return Value(fields={0: Value(function=UNIQUE_TERMS), 1: Value(),
                         2: Value(function=UNIQUE_MODULUS), 3: Value(), 4: Value()})


def uniqueness_candidate(side):
    return Value(fields={0: tag(side+"-real"),
                         1: Value(function=UNIQUE_FIRST_RATE if side == "first" else UNIQUE_SECOND_RATE),
                         2: Value(function=UNIQUE_FIRST_LAW if side == "first" else UNIQUE_SECOND_LAW)})


def uniqueness_query():
    # p=2; p+1=3; rates are 7 and 10; the response extensions are 13 and 11.
    return Value(tags=frozenset({"query"}),
                 fields={i: Value(number=n) for i,n in enumerate((2,20,21,3,4))})


def uniqueness_bank():
    return Value(tags=frozenset({"bank-current"}),function=UNIQUE_BANK)


def uniqueness_packet():
    return Value(fields={0: tag("term-step"), 1: tag("first-step"), 2: tag("second-step"),
                         3: tag("first-near"), 4: tag("second-near"), 5: tag("composed-near")})


class NativeUniquenessAnalysis(Analysis):
    def __init__(self,*args,watched="",mode="mediate",**kwargs):
        super().__init__(*args,target="",capture=True,**kwargs)
        self.watched,self.mode=watched,mode

    def run(self,name,args):
        count=int(name == self.watched)
        if name == "l_native_unique_nat_add":
            if any(value.number is None for value in args):
                raise ValueError("Unknown native uniqueness precision arithmetic")
            return Value(number=args[0].number+args[1].number),count,count
        if name == UNIQUE_MODULUS:
            if args[0].number != 3:
                raise ValueError("Native uniqueness modulus lost p+1")
            return Value(number=13),count,count
        if name in (UNIQUE_FIRST_RATE,UNIQUE_SECOND_RATE):
            if args[0].number != 3:
                raise ValueError("Native candidate rate lost p+1")
            return Value(number=7 if name == UNIQUE_FIRST_RATE else 10),count,count
        if name == UNIQUE_TERMS:
            if args[0].number != 13:
                raise ValueError("Native uniqueness term lost modulus index")
            return tag("term-real"),count,count
        if name == UNIQUE_BANK:
            if args[0].number != 13:
                raise ValueError("Native uniqueness bank lost modulus index")
            return tag("term-current"),count,count
        if name == ENV:
            role=next((side for side in ("term","first","second")
                       if args[2].retained() == frozenset({side+"-real"})),None)
            if role is None:
                raise ValueError("Native uniqueness changed one Real environment")
            return tag(role+"-environment"),count,count
        if name == EXEC:
            role=next((side for side in ("term","first","second")
                       if args[2].retained() == frozenset({side+"-real"})),None)
            if role is None:
                raise ValueError("Unknown native uniqueness execution role")
            require(args[3],role+"-current","Native uniqueness execution reset its current archive")
            expected={"term":3,"first":20,"second":21}[role]
            if args[4].number != expected:
                raise ValueError("Native uniqueness execution changed its response precision")
            hit=int(self.watched == "execute-"+role)
            return tag(role+"-step"),count+hit,count+hit
        if name in (UNIQUE_FIRST_LAW,UNIQUE_SECOND_LAW):
            side="first" if name == UNIQUE_FIRST_LAW else "second"
            for slot,expected in ((0,3),(1,13),(2,3),(3,20 if side == "first" else 21)):
                if args[slot].number != expected:
                    raise ValueError("Native convergence lost a positive precision/index extension")
            for slot,expected in ((4,"term-current"),(5,side+"-current"),
                                  (6,"term-step"),(7,side+"-step")):
                require(args[slot],expected,"Native convergence lost its exact shared term/candidate Step")
            expected_extension=13 if side == "first" else 11
            if args[10].number != expected_extension:
                raise ValueError("Native convergence lost a positive precision/index extension")
            return tag(side+"-near"),count,count
        if name == UNIQUE_SYM:
            require(args[0],"first-near","Native uniqueness symmetrizes the wrong convergence")
            return tag("symmetric-first"),count,count
        if name == UNIQUE_COMPOSE:
            require(args[0],"symmetric-first","Native uniqueness composition lost its first direction")
            require(args[1],"second-near","Native uniqueness composition lost its second convergence")
            return tag("composed-near"),count,count
        if name == UNIQUE_MEDIATE and self.mode != "mediate":
            require(args[5],"bank-current","Native trace mediation reset its incoming bank")
            require(args[6],"first-current","Native trace mediation reset its first archive")
            require(args[7],"second-current","Native trace mediation reset its second archive")
            require(args[8],"query","Native trace mediation changed its query")
            return uniqueness_packet(),count,count
        if name == STEP_NEXT:
            role=next((side for side in ("term","first","second")
                       if args[0].retained() == frozenset({side+"-environment"})),None)
            if role is None:
                raise ValueError("Native trace successor changed environment")
            require(args[1],role+"-current","Native trace successor changed incoming archive")
            require(args[3],role+"-step","Native trace successor lost its exact owned Step")
            expected={"term":3,"first":20,"second":21}[role]
            if args[2].number != expected:
                raise ValueError("Native trace successor changed response precision")
            return tag(role+"-next"),count,count
        if name in (UNIQUE_TRACE,UNIQUE_PROJECT):
            if self.mode == "future":
                bank=args[5]
                if bank.function != N+"initialBank" or bank.fixed != 3:
                    raise ValueError("Native future did not use the declared initial bank")
                require(args[6],"first-current","Native future changed first archive")
                require(args[7],"second-current","Native future changed second archive")
                require(args[8],"queries","Native future changed query list")
                if name == UNIQUE_TRACE:
                    return tag("whole-native-trace"),count,count
                require(args[9],"whole-native-trace","Native future projection lost its one produced rich trace")
                return tag("whole-native-numerical-trace"),count,count
            bank=args[5]
            if bank.function != N+"updateBank___boxed" or bank.fixed != 6:
                raise ValueError("Native trace recursion lost the updated current bank")
            require(bank.fields[3],"bank-current","Native trace bank update lost the incoming bank")
            if bank.fields[4].number != 13:
                raise ValueError("Native trace bank update changed the visited index")
            require(bank.fields[5],"term-next","Native trace bank update lost the term successor")
            require(args[6],"first-next","Native trace recursion lost first successor")
            require(args[7],"second-next","Native trace recursion lost second successor")
            require(args[8],"remaining","Native trace recursion changed query tail")
            if name == UNIQUE_TRACE:
                return tag("native-rich-tail"),count,count
            require(args[9],"native-rich-tail","Native projection lost the owned rich tail")
            return tag("native-numerical-tail"),count,count
        if name in (N+"toEffectiveFamily",N+"asExecutedCandidate",R+"executeReal"):
            raise ValueError("Native uniqueness reintroduced the downstream readout realization")
        value,low,high=super().run(name,args)
        return value,low+count,high+count


def run_native_uniqueness(functions,params,entry,args,watched="",expected=0,mode="mediate"):
    value,low,high=NativeUniquenessAnalysis(functions,params,base["shared"]["reachable"],
        watched=watched,mode=mode).run(entry,args)
    if (low,high) != (expected,expected):
        raise ValueError(f"Native uniqueness multiplicity {watched}: expected {expected}, got [{low},{high}]")
    return value


def native_uniqueness_cons_branch(functions,params,entry,query_slot):
    condition=params[entry][query_slot]
    pattern=(r'\{\s*_start:\s*\{\s*if \(lean_obj_tag\('+re.escape(condition)+
             r'\) == 0\)\s*(\{.*\})\s*else\s*(\{.*\})\s*\}\s*\}')
    match=re.fullmatch(pattern,functions[entry],re.S)
    if match is None:
        raise ValueError("Pinned native uniqueness list-branch shape changed")
    alias="l_native_unique_cons_"+str(query_slot)+"_"+entry.rsplit("_",1)[-1]
    return dict(functions,**{alias:match[2]}),dict(params,**{alias:params[entry]}),alias


def check_native_uniqueness_mediate(functions,params):
    args=[Value(),Value(),uniqueness_family(),uniqueness_candidate("first"),
          uniqueness_candidate("second"),uniqueness_bank(),tag("first-current"),
          tag("second-current"),uniqueness_query()]
    for watched in ("execute-term","execute-first","execute-second",UNIQUE_FIRST_LAW,UNIQUE_SECOND_LAW,UNIQUE_COMPOSE):
        result=run_native_uniqueness(functions,params,UNIQUE_MEDIATE,args,watched,1)
        for slot,expected in ((0,"term-step"),(1,"first-step"),(2,"second-step"),
                              (3,"first-near"),(4,"second-near"),(5,"composed-near")):
            require(result.fields[slot],expected,"Native mediation lost a stored exact resource")


def check_native_uniqueness_trace(functions,params):
    functions,params,entry=native_uniqueness_cons_branch(functions,params,UNIQUE_TRACE,8)
    query=uniqueness_query()
    args=[Value(),Value(),uniqueness_family(),uniqueness_candidate("first"),
          uniqueness_candidate("second"),uniqueness_bank(),tag("first-current"),
          tag("second-current"),Value(fields={0:query,1:tag("remaining")})]
    for watched,expected in ((UNIQUE_MEDIATE,1),(UNIQUE_TRACE,1),(EXEC,0)):
        result=run_native_uniqueness(functions,params,entry,args,watched,expected,"trace")
        require(result.fields[5].fields[0],"term-step","Native trace lost its one mediation packet")
        require(result.fields[6],"native-rich-tail","Native trace lost its owned continuation")


def check_native_uniqueness_projection(functions,params):
    functions,params,entry=native_uniqueness_cons_branch(functions,params,UNIQUE_PROJECT,8)
    rich=Value(fields={5:uniqueness_packet(),6:tag("native-rich-tail")})
    args=[Value(),Value(),uniqueness_family(),uniqueness_candidate("first"),
          uniqueness_candidate("second"),uniqueness_bank(),tag("first-current"),
          tag("second-current"),Value(fields={0:uniqueness_query(),1:tag("remaining")}),rich]
    for watched,expected in ((UNIQUE_PROJECT,1),(UNIQUE_MEDIATE,0),(EXEC,0),
                             (UNIQUE_FIRST_LAW,0),(UNIQUE_SECOND_LAW,0)):
        result=run_native_uniqueness(functions,params,entry,args,watched,expected,"projection")
        for slot,expected_tag in ((4,"first-step"),(5,"second-step"),
                                  (6,"composed-near"),(7,"native-numerical-tail")):
            require(result.fields[slot],expected_tag,"Native numerical projection reconstructed/lost a result")


def check_native_uniqueness_future(functions,params):
    args=[Value(),Value(),uniqueness_family(),uniqueness_candidate("first"),
          uniqueness_candidate("second"),tag("first-current"),tag("second-current"),tag("queries")]
    for watched in (UNIQUE_TRACE,UNIQUE_PROJECT):
        require(run_native_uniqueness(functions,params,UNIQUE_FUTURE,args,watched,1,"future"),
                "whole-native-numerical-trace","Native future lost the shared rich trace")
    body=functions[UNIQUE]
    if N+"nativeNumericalFutures" not in body:
        raise ValueError("nativeUnique does not derive its result from native futures")
    for forbidden in (N+"toEffectiveFamily",N+"asExecutedCandidate",N+"realizedFamily",
                      PREFIX+"RelationalRealLimitUniqueness_unique"):
        if forbidden in body or forbidden in functions[N+"nativeNumericalFutures"] or forbidden in functions[UNIQUE_FUTURE]:
            raise ValueError("Native uniqueness reintroduced its old downstream mediation")


def reject_native_uniqueness(check,functions,params,label,prefix):
    try:
        check(functions,params)
    except ValueError as error:
        if not str(error).startswith(prefix):
            raise ValueError(f"Wrong native uniqueness mutation refusal {label}: {error}") from error
        print("REAL_NATIVE_UNIQUENESS_MUTATION_REJECTED "+label)
        return
    raise ValueError("Native uniqueness mutation accepted: "+label)


def produce_args():
    return [Value(),Value(),family(),bank(),tag("current-journal"),tag("p")]


def check_production(functions,params):
    for watched,count in ((EXEC,1),(NORMAL,1),(EXECUTOR,2),(R+"executeReal",0)):
        if run(functions,params,PRODUCE,produce_args(),watched,count) != production():
            raise ValueError("Native production discarded exact source/grouping/target")


def check_next(functions,params):
    args=[Value(),Value(),family(),archive(),tag("p"),production()]
    for watched,count in ((STEP_NEXT,1),(EXEC,0),(NORMAL,0),(JOURNAL,2)):
        value=run(functions,params,NEXT,args,watched,count)
        update=value.fields[0]
        if update.function != N+"updateBank___boxed" or update.fixed != 6:
            raise ValueError("Native bank update closure changed")
        for slot,wanted in ((3,bank()),(4,tag("diagonal-index")),(5,tag("native-successor"))):
            if update.fields[slot] != wanted:
                raise ValueError("Native bank reset/discarded successor")
        require(value.fields[1],"after-grouping-journal","Native next lost completed journal")
        retained=Value(fields={0:bank(),1:Value(fields={0:tag("current-journal"),1:Value(fields={0:tag("p"),1:production()})})})
        if value.fields[3].fields[0] != retained or value.fields[2].fields[1].fields[0] != retained:
            raise ValueError("Native installed/retained resource is not shared production")


def check_normalization(functions,params):
    args=[Value(),Value(),family(),bank(),tag("p"),source_execution()]
    for watched,count in ((CODE,2),(LAW,1),(TRANSPORT,1),(EXEC,0)):
        if run(functions,params,NORMAL,args,watched,count,True) != charge():
            raise ValueError("Native normalizer did not retain source charge")


def check_live(functions,params):
    value=run(functions,params,SERVICE,[Value(),Value(),family()])
    closure=value.fields[9]
    if closure.function != N+"nativeLiveStep___boxed" or closure.fixed != 2 or closure.fields != {0:Value(function=KERNELS),1:Value(function=MOD)}:
        raise ValueError("Native live closure captures rich family/terms/service")
    for watched,count in ((KERNELS,1),(KSTEP,1),(ANSWER,1),(EXEC,0),(NORMAL,0)):
        result=run(functions,params,LIVE,[Value(function=KERNELS),Value(function=MOD),tag("p")],watched,count)
        require(result.fields[0].fields[0],"live-code","Native live next lost answer")
        require(result.fields[1],"live-code","Native live event lost answer")


def check_observation(functions,params):
    args=[family()]+[tag(x) for x in ("coarse","n","r","p","term-archive")]+[archive(),tag("received-term"),production()]+[tag(x) for x in ("hn","hr","hs")]
    for watched,count in ((EXEC,0),(NORMAL,0),(LAW,1),(MONO,1)):
        value=run(functions,params,OBSERVE,args,watched,count)
        for slot,wanted in ((0,"received-term"),(2,"current-native-archive"),(3,"owned-diagonal"),(4,"exact-cauchy-near"),(5,"exact-cauchy-near")):
            require(value.fields[slot],wanted,"Native observation dropped received resource/Near")
        if value.fields[1] != production():
            raise ValueError("Native observation replaced current limit")


def reject(check,functions,params,label,prefix):
    try:
        check(functions,params)
    except ValueError as error:
        if not str(error).startswith(prefix):
            raise ValueError(f"Wrong mutation refusal {label}: {error}") from error
        print("REAL_NATIVE_CAUCHY_MUTATION_REJECTED "+label)
        return
    raise ValueError("Native mutation accepted: "+label)


def shared_allocation_path(body):
    def closing(start):
        depth=0
        for index in range(start,len(body)):
            depth += (body[index]=="{")-(body[index]=="}")
            if depth==0:
                return index
        raise ValueError("Unbalanced pinned allocation branch")
    while match:=re.search(r'if \(v_isShared\w* == 0\)\s*\{',body):
        yes=body.index("{",match.start());end=closing(yes)
        tail=re.match(r'\s*else\s*\{',body[end+1:])
        if tail is None:
            raise ValueError("Pinned shared allocation has no fallback")
        no=end+1+tail.end()-1;stop=closing(no)
        body=body[:match.start()]+body[no+1:stop]+body[stop+1:]
    return body


def main():
    texts=[p.read_text(encoding="utf-8") for p in sorted((ROOT/".lake/build/ir").rglob("*.c"))]
    functions={}
    for text in texts:
        functions.update(base["shared"]["bodies"](text));base["add_static_objects"](functions,text)
    functions={n:re.sub(r'lean_unsigned_to_nat\((\d+)u\)',r'lean_box(\1)',re.sub(r'\(\(lean_object\*\)\(((?:l|lp)_\w+)\)\)',r'\1',body)) for n,body in functions.items()}
    # Avoid interpreting an impossible unique reuse after the same production
    # has been retained. We test the valid all-shared branch, not RC semantics.
    functions[NEXT]=shared_allocation_path(functions[NEXT])
    params=base["parameters"](texts)
    for check in (check_production,check_normalization,check_next,check_live,check_observation):
        check(functions,params);print("REAL_NATIVE_CAUCHY_ROUTE_OK "+check.__name__)
    cases=[(check_production,N+"searchNativeSource___redArg",EXEC,0,s,"Native execution lost received") for s in (2,3,4)]
    cases += [(check_production,PRODUCE,EXECUTOR,i,3,"Native program reset") for i in (0,1)]
    cases += [(check_production,N+"nativeGroupingProgram___redArg___lam__3",NORMAL,0,5,"Native grouping did not consume")]
    cases += [(check_production,PRODUCE,"lean_ctor_set",i,2,"Native production discarded") for i in (0,1)]
    cases += [(check_next,NEXT,STEP_NEXT,0,s,"Native continuation lost") for s in (0,1,2,3)]
    cases += [(check_observation,OBSERVE,"lean_apply_13",0,s,"Native convergence lost received") for s in range(1,14)]
    cases += [(check_live,LIVE,"lean_apply_2",0,s,"Native live step") for s in (1,2)]
    cases += [(check_live,LIVE,"lean_apply_1",2,1,"Native live answer")]
    cases += [(check_normalization,N+"nativeSpecification___redArg",CODE,0,3,"Native code does not read")]
    cases += [(check_normalization,N+"nativeSpecification___redArg___lam__1","lean_apply_13",0,s,"Native normalizer Cauchy lost") for s in (6,7,8,9)]
    cases += [(check_production,N+"nativeSourceProgram___lam__2",N+"searchNativeSource___redArg",0,4,"Native execution lost received")]
    cases += [(check_next,NEXT,"lean_closure_set",s,2,"Native bank reset/discarded") for s in (3,4,5)]
    for i,(check,entry,callee,occurrence,slot,prefix) in enumerate(cases):
        reject(check,mutate(functions,entry,callee,occurrence,slot,"lean_box(0)"),params,str(i)+"-"+entry+"-"+str(slot),prefix)
    reject(check_live,mutate(functions,SERVICE,"lean_closure_set",12,2,params[SERVICE][2]),params,"live-captures-rich-family","Native live closure captures")
    alias="l_native_duplicate_original"
    broken,changed=dict(functions),dict(params)
    broken[alias],changed[alias]=functions[PRODUCE],params[PRODUCE]
    injected="lean_object* ignored; ignored = "+alias+"("+",".join(params[PRODUCE])+");"
    broken[PRODUCE]=functions[PRODUCE].replace("{","{"+injected,1)
    reject(check_production,broken,changed,"duplicate-valid-native-production","Native multiplicity")
    # Replaying a second identical action must fail even if the first target
    # is the only one retained. Concrete callback arguments remain unchanged.
    entry=N+"nativeGroupingProgram___redArg___lam__3"
    alias="l_native_duplicate_grouping"
    broken,changed=dict(functions),dict(params)
    broken[alias],changed[alias]=functions[entry],params[entry]
    injected="lean_object* ignored; ignored = "+alias+"("+",".join(params[entry])+");"
    broken[entry]=functions[entry].replace("{","{"+injected,1)
    reject(check_production,broken,changed,"duplicate-valid-grouping-action","Native multiplicity")
    unique_functions={name:body.replace("lean_nat_add(","l_native_unique_nat_add(")
                      for name,body in functions.items()}
    for name,arity in ((UNIQUE_MEDIATE,9),(UNIQUE_TRACE,9),(UNIQUE_PROJECT,10),
                       (UNIQUE_FUTURE,8),(UNIQUE,5)):
        if len(params.get(name,[])) != arity:
            raise ValueError("Missing exact native uniqueness C definition/arity: "+name)
    for check in (check_native_uniqueness_mediate,check_native_uniqueness_trace,
                  check_native_uniqueness_projection,check_native_uniqueness_future):
        check(unique_functions,params)
        print("REAL_NATIVE_UNIQUENESS_ROUTE_OK "+check.__name__)
    for occurrence in range(3):
        broken=mutate(unique_functions,UNIQUE_MEDIATE,EXEC,occurrence,3,"lean_box(0)")
        reject_native_uniqueness(check_native_uniqueness_mediate,broken,params,
          "reset-execution-"+str(occurrence),"Native uniqueness execution reset its current archive")
    for occurrence in range(2):
        for slot in (5,6,7,8,11):
            broken=mutate(unique_functions,UNIQUE_MEDIATE,"lean_apply_11",occurrence,slot,"lean_box(0)")
            prefix=("Native convergence lost a positive precision/index extension" if slot == 11
                    else "Native convergence lost its exact shared term/candidate Step")
            reject_native_uniqueness(check_native_uniqueness_mediate,broken,params,
              f"convergence-{occurrence}-lost-{slot}",prefix)
    for slot in (5,6,7):
        broken=mutate(unique_functions,UNIQUE_TRACE,UNIQUE_TRACE,0,slot,params[UNIQUE_TRACE][slot])
        prefix=("Native trace recursion lost the updated current bank" if slot == 5 else
                "Native trace recursion lost first successor" if slot == 6 else
                "Native trace recursion lost second successor")
        reject_native_uniqueness(check_native_uniqueness_trace,broken,params,
          "reset-recursive-successor-"+str(slot),prefix)
    broken=mutate(unique_functions,UNIQUE_MEDIATE,UNIQUE_SYM,0,0,"lean_box(0)")
    reject_native_uniqueness(check_native_uniqueness_mediate,broken,params,
      "lost-first-direction","Native uniqueness symmetrizes the wrong convergence")
    broken=mutate(unique_functions,UNIQUE_MEDIATE,UNIQUE_COMPOSE,0,1,"lean_box(0)")
    reject_native_uniqueness(check_native_uniqueness_mediate,broken,params,
      "lost-second-near","Native uniqueness composition lost its second convergence")
    alias="l_native_unique_duplicate_mediate"
    broken,changed=dict(unique_functions),dict(params)
    broken[alias],changed[alias]=unique_functions[UNIQUE_MEDIATE],params[UNIQUE_MEDIATE]
    injected="lean_object* ignored; ignored = "+alias+"("+",".join(params[UNIQUE_MEDIATE])+");"
    broken[UNIQUE_MEDIATE]=unique_functions[UNIQUE_MEDIATE].replace("{","{"+injected,1)
    reject_native_uniqueness(check_native_uniqueness_mediate,broken,changed,
      "duplicate-valid-native-mediation","Native uniqueness multiplicity")
    print("REAL_NATIVE_CAUCHY_CODEGEN_OK: nine routes; owned diagonal/charge, direct native uniqueness mediation/continuation, current journals, shared target and compact visible captures; same-index pure replay and callback internals/Prop formation excluded")


if __name__ == "__main__":
    try:
        main()
    except (ValueError,KeyError) as error:
        print("REAL_NATIVE_CAUCHY_CODEGEN_FAILED "+str(error),file=sys.stderr)
        raise SystemExit(1)

#include "Dataflow.h"
#include <algorithm>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace llvm;

typedef  std::unordered_set<Value *> ValueSet;
typedef  std::unordered_set<Function *> FunctionSet;
typedef  std::unordered_map<Value *, ValueSet> valueMap;



// struct LivenessInfo {
//    std::set<Instruction *> LiveVars;             /// Set of variables which are live
//    LivenessInfo() : LiveVars() {}
//    LivenessInfo(const LivenessInfo & info) : LiveVars(info.LiveVars) {}
  
//    bool operator == (const LivenessInfo & info) const {
//        return LiveVars == info.LiveVars;
//    }
// };

// inline raw_ostream &operator<<(raw_ostream &out, const LivenessInfo &info) {
//     for (std::set<Instruction *>::iterator ii=info.LiveVars.begin(), ie=info.LiveVars.end();
//          ii != ie; ++ ii) {
//        const Instruction * inst = *ii;
//        out << inst->getName();
//        out << " ";
//     }
//     return out;
// }

	
// class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
// public:
//    LivenessVisitor() {}
//    void merge(LivenessInfo * dest, const LivenessInfo & src) override {
//        for (std::set<Instruction *>::const_iterator ii = src.LiveVars.begin(), 
//             ie = src.LiveVars.end(); ii != ie; ++ii) {
//            dest->LiveVars.insert(*ii);
//        }
//    }

//    void compDFVal(Instruction *inst, LivenessInfo * dfval) override{
//         if (isa<DbgInfoIntrinsic>(inst)) return;
//         dfval->LiveVars.erase(inst);
//         for(User::op_iterator oi = inst->op_begin(), oe = inst->op_end();
//             oi != oe; ++oi) {
//            Value * val = *oi;
//            if (isa<Instruction>(val)) 
//                dfval->LiveVars.insert(cast<Instruction>(val));
//        }
//    }
// };


// class Liveness : public FunctionPass {
// public:

//    static char ID;
//    Liveness() : FunctionPass(ID) {} 

//    bool runOnFunction(Function &F) override {
//        F.dump();
//        LivenessVisitor visitor;
//        DataflowResult<LivenessInfo>::Type result;
//        LivenessInfo initval;

//        compBackwardDataflow(&F, &visitor, &result, initval);
//        printDataflowResult<LivenessInfo>(errs(), result);
//        return false;
//    }
// };

struct pInfo
{
    valueMap pMap;        
    valueMap domainMap;  
    pInfo() : pMap(), domainMap() {}
    pInfo(const pInfo &other)
        : pMap(other.pMap), domainMap(other.domainMap)
    {
    }
    bool operator==(const pInfo &other) const
    {
        return (pMap == other.pMap) && (domainMap == other.domainMap);
    }
    bool operator!=(const pInfo &other) const
    {
        return (pMap != other.pMap) || (domainMap != other.domainMap);
    }
    pInfo &operator=(const pInfo &other)  // copy assignment
    {
        pMap = other.pMap;
        domainMap = other.domainMap;
        return *this;
    }
};

struct cmp
{
    bool operator()(const CallInst *leftC, const CallInst *rightC)
    {
        return (leftC->getDebugLoc().getLine() < rightC->getDebugLoc().getLine());
    }
};


//result printf
inline raw_ostream &operator<<(raw_ostream &out, const valueMap &v)
{
    out << "{ ";
    for (auto i = v.begin(), e = v.end(); i != e; ++i)
    {
        out << i->first->getName() << " " << i->first << " -> ";
        for (auto ii = i->second.begin(), ie = i->second.end(); ii != ie; ++ii)
        {
            if (ii != i->second.begin())
            {
                errs() << ", ";
            }
            out << (*ii)->getName() << " " << (*ii);
        }
        out << " ; ";
    }
    out << "}";
    return out;
}


//test using
inline raw_ostream &operator<<(raw_ostream &out, const pInfo &info)
{
    out << "pMap : " << info.pMap <<"\ndomainMap : " << info.domainMap << "\n";
    return out;
}

FunctionSet rollBackSet(Value *v, pInfo *pinfo)
{
    FunctionSet ret;
    ValueSet worklist;
    if (auto *F = dyn_cast<Function>(v)){
        ret.insert(F);
        return ret;
    }

    if (pinfo->pMap.count(v)){
        worklist.insert(pinfo->pMap[v].begin(), pinfo->pMap[v].end());
    }

    while (!worklist.empty()){
        Value *i = *worklist.begin();
        worklist.erase(worklist.begin());
        if (auto *F = dyn_cast<Function>(i)){ret.insert(F);}
        else{worklist.insert(pinfo->pMap[i].begin(), pinfo->pMap[i].end());}
    }
    return ret;
}

class PointToVisitor : public DataflowVisitor<struct pInfo>
{
public:
    FunctionSet fun_Set;
    std::map<CallInst *, FunctionSet, cmp> call_Map;

    PointToVisitor() : fun_Set(), call_Map() {}

    void merge(pInfo *dest, const pInfo &src) override
    {
        for (auto i = src.pMap.begin(), e = src.pMap.end(); i != e; ++i){
            dest->pMap[i->first].insert(i->second.begin(), i->second.end());
        }
        for (auto i = src.domainMap.begin(), e = src.domainMap.end(); i != e; ++i){
            dest->domainMap[i->first].insert(i->second.begin(), i->second.end());
        }
    }

    void compDFVal(Instruction *inst, DataflowResult<pInfo>::Type *result) override
    {

    //     /*
    // // if (auto gep = dyn_cast<GetElementPtrInst>(inst)) {
    // // //   /* dfval->clear(gep).insert(gep->getPointerOperand()); */
    // // //   /* return; */

    // //   auto p = gep->getPointerOperand();
    // //   if (dfval->isNotEmpty(p))
    // //     dfval->clear(gep) = dfval->getPTS(p);
    // //   else {
    // //     /* errs() << *p << "\n"; */
    // //     /* errs() << *gep << "\n"; */
    // //     /* errs() << *dfval << "\n"; */
    // //     dfval->setNotReady(gep);
    // //     /* errs() << *inst << "\n"; */
    // //     /* errs() << *p << "\n"; */
    // //   }
    // // }

    // // if (auto bitcast = dyn_cast<BitCastInst>(inst)) {
    // //   /* errs() << "777777" << "\n"; */
    // //   Value *from = bitcast->User::getOperand(0);

    // //   /* errs() << *from << "\n"; */

    // //   dfval->clear(bitcast).insert(from);
    // // }
    //     */
        if (isa<IntrinsicInst>(inst)){
            if (auto *MCI = dyn_cast<MemCpyInst>(inst)){    //ANCHOR 还是TAG，前面变量的初始化基本都是一样的，
                parseMemInst(MCI, result);
            }
            else{
                (*result)[inst].second = (*result)[inst].first;
                return;
            }
        }else if (auto *PHI = dyn_cast<PHINode>(inst)){
            parsePhi(PHI, result);
        }else if (auto *CI = dyn_cast<CallInst>(inst)){
            parseCInst(CI, result);
        }else if (auto *SI = dyn_cast<StoreInst>(inst)){
            parseStore(SI, result);
        }else if (auto *LI = dyn_cast<LoadInst>(inst)){
            parseLoad(LI, result);
        }else if (auto *RI = dyn_cast<ReturnInst>(inst)){
            parseRet(RI, result);
        }else if (auto *GEP = dyn_cast<GetElementPtrInst>(inst)){
            parseElePtr(GEP, result);
        }else if (auto *BCI = dyn_cast<BitCastInst>(inst)){
            parseBit(BCI, result);
        }else{      

            //set not ready
            (*result)[inst].second = (*result)[inst].first;
        }
    }

    void parseLoad(LoadInst *LI, DataflowResult<pInfo>::Type *result)
    {
        pInfo pinfo  = (*result)[LI].first;
        pinfo.pMap[LI].clear();
        if (auto *GEP = dyn_cast<GetElementPtrInst>(LI->getPointerOperand()))
        {
            if (!pinfo.pMap[GEP->getPointerOperand()].empty())
            {
                ValueSet &pts1 = pinfo.pMap[GEP->getPointerOperand()];
                for (auto i = pts1.begin(), e = pts1.end(); i != e; ++i)
                {
                    Value *v = *i;
                    ValueSet &pts2 = pinfo.domainMap[v];
                    pinfo.pMap[LI].insert(pts2.begin(), pts2.end());
                }
            }
            else
            {
                ValueSet &pts = pinfo.domainMap[GEP->getPointerOperand()];
                pinfo.pMap[LI].insert(pts.begin(), pts.end());
            }
        }
        else
        {
            ValueSet &pts = pinfo.pMap[LI->getPointerOperand()];
            pinfo.pMap[LI].insert(pts.begin(), pts.end());
        }
        (*result)[LI].second = pinfo;
    }

    void parseStore(StoreInst *SI, DataflowResult<pInfo>::Type *result)
    {
        pInfo pinfo = (*result)[SI].first;
        ValueSet pts_to_insert;
        if (!pinfo.pMap[SI->getValueOperand()].empty())
        {
            ValueSet &pts = pinfo.pMap[SI->getValueOperand()];
            pts_to_insert.insert(pts.begin(), pts.end());
        }
        else
        {
            pts_to_insert.insert(SI->getValueOperand());
        }

        if (auto *GEP = dyn_cast<GetElementPtrInst>(SI->getPointerOperand()))
        {
            if (!pinfo.pMap[GEP->getPointerOperand()].empty())
            {
                ValueSet &pts = pinfo.pMap[GEP->getPointerOperand()];
                for (auto i = pts.begin(), e = pts.end(); i != e; ++i)
                {
                    Value *v = *i;
                    pinfo.domainMap[v].clear();
                    pinfo.domainMap[v].insert(pts_to_insert.begin(),
                                                 pts_to_insert.end());
                }
            }
            else
            {
                pinfo.domainMap[GEP->getPointerOperand()].clear();
                pinfo.domainMap[GEP->getPointerOperand()].insert(pts_to_insert.begin(),
                                                                    pts_to_insert.end());
            }
        }
        else
        {
            pinfo.pMap[SI->getPointerOperand()].clear();
            pinfo.pMap[SI->getPointerOperand()].insert(pts_to_insert.begin(),
                                                         pts_to_insert.end());
        }
        (*result)[SI].second = pinfo;
    }

    void parsePhi(PHINode *PHI, DataflowResult<pInfo>::Type *result)
    {
        pInfo pinfo = (*result)[PHI].first;
        pinfo.pMap[PHI].clear();
        for (Value *V : PHI->incoming_values())
        {
            if (isa<ConstantPointerNull>(V))              continue;
            if (isa<Function>(V)){
                pinfo.pMap[PHI].insert(V);
            }else{
                ValueSet &v_set = pinfo.pMap[V];
                pinfo.pMap[PHI].insert(v_set.begin(), v_set.end());
            }
        }
        (*result)[PHI].second = pinfo;
    }


//fix bug for test 25 && test 28
//
//
    void parseCInst(CallInst *CI, DataflowResult<pInfo>::Type *result)
    {
        pInfo dfval = (*result)[CI].first;

        FunctionSet calleeSet = rollBackSet(CI->getCalledValue(), &dfval);
        call_Map[CI].clear();call_Map[CI].insert(calleeSet.begin(), calleeSet.end());

        // ci call list 
        if (CI->getCalledFunction() && CI->getCalledFunction()->isDeclaration()){
            (*result)[CI].second = (*result)[CI].first;
            return;
        }

        for (auto i = calleeSet.begin(), e = calleeSet.end(); i != e; ++i){
            Function *callee = *i;
            if (callee->isDeclaration())
                continue;
            // construct arg_map to install arguments
            std::unordered_map<Value *, Argument *> arg_map;
            for (unsigned arg_i = 0; arg_i < CI->getNumArgOperands(); ++arg_i){
                Value *caller_arg = CI->getArgOperand(arg_i);
                if (!caller_arg->getType()->isPointerTy())
                    continue;
                Argument *callee_arg = callee->arg_begin() + arg_i;
                arg_map.insert(std::make_pair(caller_arg, callee_arg));
            }

            pInfo &callee_dfval_in = (*result)[&*inst_begin(callee)].first;
            pInfo old_callee_dfval_in = callee_dfval_in;
            pInfo tmp_dfval = (*result)[CI].first;
            if (arg_map.empty()){
                merge(&((*result)[CI].second), (*result)[CI].first);
                continue;
            }

            for (auto pi = tmp_dfval.pMap.begin(), pe = tmp_dfval.pMap.end();
                 pi != pe; ++pi){
                for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai){
                    if (pi->second.count(ai->first) && !isa<Function>(ai->first)){
                        pi->second.erase(ai->first);
                        pi->second.insert(ai->second);
                    }
                }
            }
            for (auto pi = tmp_dfval.domainMap.begin(),
                      pe = tmp_dfval.domainMap.end();
                 pi != pe; ++pi){
                for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai){
                    if (pi->second.count(ai->first) && !isa<Function>(ai->first)){
                        pi->second.erase(ai->first);
                        pi->second.insert(ai->second);
                    }
                }
            }
            for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai){
                if (tmp_dfval.pMap.count(ai->first)){
                    ValueSet v_set = tmp_dfval.pMap[ai->first];
                    tmp_dfval.pMap.erase(ai->first);
                    tmp_dfval.pMap[ai->second].insert(v_set.begin(), v_set.end());
                }
                if (tmp_dfval.domainMap.count(ai->first)){
                    ValueSet v_set = tmp_dfval.domainMap[ai->first];
                    tmp_dfval.domainMap.erase(ai->first);
                    tmp_dfval.domainMap[ai->second].insert(v_set.begin(), v_set.end());
                }
            }
            for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai){
                if (isa<Function>(ai->first))
                {
                    tmp_dfval.pMap[ai->second].insert(ai->first);
                }
            }

            merge(&callee_dfval_in, tmp_dfval);
            if (old_callee_dfval_in != callee_dfval_in)
            {
                fun_Set.insert(callee);
                // errs()<< callee->getName()<<endl;
            }
        }
    }

//returnInst is not fouded by local casted
    void parseRet(ReturnInst *RI, DataflowResult<pInfo>::Type *result)
    {
        (*result)[RI].second = (*result)[RI].first;

        Function *callee = RI->getFunction();
        for (auto i = call_Map.begin(), e = call_Map.end(); i != e; ++i)
        {
            if (i->second.count(callee))
            {
                CallInst *CI = i->first;
                Function *caller = CI->getFunction();
                // construct arg_map
                std::unordered_map<Value *, Argument *> arg_map;
                for (unsigned arg_i = 0; arg_i < CI->getNumArgOperands(); ++arg_i)
                {
                    Value *caller_arg = CI->getArgOperand(arg_i);
                    if (!caller_arg->getType()->isPointerTy())
                        continue;
                    Argument *callee_arg = callee->arg_begin() + arg_i;
                    arg_map.insert(std::make_pair(caller_arg, callee_arg));
                }
                pInfo tmp_dfval = (*result)[RI].first;
                pInfo &caller_dfval_out = (*result)[CI].second;
                pInfo old_caller_dfval_out = caller_dfval_out;
                if (RI->getReturnValue() &&
                    RI->getReturnValue()->getType()->isPointerTy())
                {
                    ValueSet v_set = tmp_dfval.pMap[RI->getReturnValue()];
                    tmp_dfval.pMap.erase(RI->getReturnValue());
                    tmp_dfval.pMap[CI].insert(v_set.begin(), v_set.end());
                }
                for (auto pi = tmp_dfval.pMap.begin(), pe = tmp_dfval.pMap.end();
                     pi != pe; ++pi)
                {
                    for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai)
                    {
                        if (pi->second.count(ai->second))
                        {
                            pi->second.erase(ai->second);
                            pi->second.insert(ai->first);
                        }
                    }
                }
                for (auto pi = tmp_dfval.domainMap.begin(),
                          pe = tmp_dfval.domainMap.end();
                     pi != pe; ++pi)
                {
                    for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai)
                    {
                        if (pi->second.count(ai->second))
                        {
                            pi->second.erase(ai->second);
                            pi->second.insert(ai->first);
                        }
                    }
                }
                for (auto ai = arg_map.begin(), ae = arg_map.end(); ai != ae; ++ai)
                {
                    if (tmp_dfval.pMap.count(ai->second))
                    {
                        ValueSet v_set = tmp_dfval.pMap[ai->second];
                        tmp_dfval.pMap.erase(ai->second);
                        tmp_dfval.pMap[ai->first].insert(v_set.begin(), v_set.end());
                    }
                    if (tmp_dfval.domainMap.count(ai->second))
                    {
                        ValueSet v_set = tmp_dfval.domainMap[ai->second];
                        tmp_dfval.domainMap.erase(ai->second);
                        tmp_dfval.domainMap[ai->first].insert(v_set.begin(),
                                                                 v_set.end());
                    }
                }

                merge(&caller_dfval_out, tmp_dfval);
                if (caller_dfval_out != old_caller_dfval_out)
                {
                    fun_Set.insert(caller);
                    // errs() << caller->getName()<<endl;
                }
            }
        }
    }

    void parseElePtr(GetElementPtrInst *GEP,DataflowResult<pInfo>::Type *result)
    {
        pInfo dfval = (*result)[GEP].first;
        dfval.pMap[GEP].clear();
        if (!dfval.pMap[GEP->getPointerOperand()].empty())
        {
            dfval.pMap[GEP].insert(dfval.pMap[GEP->getPointerOperand()].begin(),
                                     dfval.pMap[GEP->getPointerOperand()].end());
        }
        else
        {
            dfval.pMap[GEP].insert(GEP->getPointerOperand());
        }
        (*result)[GEP].second = dfval;
    }

    void parseBit(BitCastInst *BCI,
                               DataflowResult<pInfo>::Type *result)
    {
        pInfo dfval = (*result)[BCI].first;
        (*result)[BCI].second = dfval;
    }


//此处为抄，待理解
    void parseMemInst(MemCpyInst *MCI, DataflowResult<pInfo>::Type *result)
    {
        pInfo dfval = (*result)[MCI].first;

        auto *BCI0 = dyn_cast<BitCastInst>(MCI->getArgOperand(0));
        auto *BCI1 = dyn_cast<BitCastInst>(MCI->getArgOperand(1));
        if (!BCI0 || !BCI1)
        {
            (*result)[MCI].second = dfval;
            return;
        }
        Value *dst = BCI0->getOperand(0);
        Value *src = BCI1->getOperand(0);
        ValueSet &src_pts = dfval.pMap[src];
        ValueSet &src_field_pts = dfval.domainMap[src];
        dfval.pMap[dst].clear();
        dfval.pMap[dst].insert(src_pts.begin(), src_pts.end());
        dfval.domainMap[dst].clear();
        dfval.domainMap[dst].insert(src_field_pts.begin(), src_field_pts.end());
        (*result)[MCI].second = dfval;
    }
};

class PointToPass : public ModulePass
{
public:
    static char ID;
private:
    DataflowResult<pInfo>::Type result_;
    FunctionSet fun_Set;

    void printCFG(const std::map<CallInst *, FunctionSet, cmp> &call_graph)
    {
        for (auto i = call_graph.begin(), e = call_graph.end(); i != e; ++i)
        {
            errs() << i->first->getDebugLoc().getLine() << " : ";
            for (auto ii = i->second.begin(), ee = i->second.end(); ii != ee; ++ii)
            {
                if (ii != i->second.begin())
                {
                    errs() << ", ";
                }

                errs() << (*ii)->getName();
            }
            errs() << "\n";
        }
        
        errs() << "------------------------------\n";
    }

public:
    PointToPass() : ModulePass(ID), result_(), fun_Set() {}
    bool runOnModule(Module &M) override
    {
        PointToVisitor visitor;

        for (auto &F : M)
        {
            if (F.isIntrinsic())
                continue;
            fun_Set.insert(&F);
        }

        while (!fun_Set.empty())
        {
            Function *F = *(fun_Set.begin());
            fun_Set.erase(fun_Set.begin());
            pInfo initval;
            //强制转换
            compForwardDataflow<struct pInfo>(F, &visitor, &result_, initval);
            fun_Set.insert(visitor.fun_Set.begin(), visitor.fun_Set.end());
            visitor.fun_Set.clear();
        }
        printCFG(visitor.call_Map);
        return false;
    }

};

char PointToPass::ID = 0;

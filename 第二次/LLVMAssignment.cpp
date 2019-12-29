//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstrTypes.h"

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <vector>
#include <set>

using namespace llvm;
using namespace std;

#if LLVM_VERSION_MAJOR >= 4
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
#endif
/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang will
 * have optnone attribute which would lead to some transform passes disabled, like mem2reg.
 */
#if LLVM_VERSION_MAJOR == 5
struct EnableFunctionOptPass: public FunctionPass {
    static char ID;
    EnableFunctionOptPass():FunctionPass(ID){}
    bool runOnFunction(Function & F) override{
        if(F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID=0;
#endif

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 2
///Updated 11/10/2017 by fargo: make all functions
///processed by mem2reg before this pass.
struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}
  set<Function *> funcSet;
  vector<set<Function *> > pathInfo;

  bool runOnModule(Module &M) override {
    // errs() << "Hello: ";
    // errs().write_escaped(M.getName()) << '\n';
    // M.dump();
    // errs()<<"------------------------------\n";

    for(auto it = M.begin();it != M.end();++it){
        if(it->isDeclaration())
            continue;
        funcSet.insert(&*it);
    }

    for(auto it = M.begin();it != M.end();++it){
        if(it->isDeclaration())
            continue;
        vector<set<Function *>> params;
        FunctionType * funT = it->getFunctionType();
        for(auto it = funT->param_begin();it != funT->param_end();++it){
            set<Function *> param;
            params.push_back(param);
        }
        Parse(&*it,params,map<Value*,set<Function*>>());
    }

    for(unsigned i=0;i<pathInfo.size();i++){
        set<Function *> &funcs = pathInfo[i];
        if(funcs.size()){
            errs()<<i<<":";
            for(auto it = funcs.begin();it != funcs.end();++it){
                if(it != funcs.begin())
                    errs()<<",";
                errs()<<(*it)->getName();
            }
            errs()<<"\n";
        }
    }
    return false;
    
  }
    //!TODO function pointer 
  set<Function *> ParseCallInst(set<BasicBlock*>&parent, CallInst * call_inst,vector<set<Function*>> args,map<Value*,set<Function*>> stackSet){
      set<Function *> callee = ParseValue(parent, call_inst->getCalledValue(),args,stackSet);
      vector<set<Function *> > argum;
      for(unsigned i = 0;i<call_inst->getNumArgOperands();i++){
          Value * argi = call_inst->getArgOperand(i);
          bool flag = argi->getType()->isPointerTy() && argi->getType()->getPointerElementType()->isFunctionTy();
          if(flag){
              argum.push_back(ParseValue(parent,argi,args,stackSet));
          }else{
              argum.push_back(set<Function*>());
          }
      }

      set<Function *> s1;
      for(auto calleeit = callee.begin();calleeit != callee.end();++calleeit){
          Function * callee = *calleeit;
          unsigned line = call_inst->getDebugLoc().getLine();
          while(pathInfo.size() <= call_inst->getDebugLoc().getLine())
            pathInfo.push_back(set<Function *>());
          pathInfo[line].insert(callee);
          if(funcSet.count(callee) && parent.count(&callee->getEntryBlock()) == 0){set<Function *> reti = Parse(callee,argum,stackSet);
              for(auto it = reti.begin();it != reti.end();++it){
                  s1.insert(*it);
              }
          }
      }
      return s1;
  }

  set<Function *> ParseValue(set<BasicBlock*> &parent,Value * val,vector<set<Function*>> &args,map<Value*,set<Function*>> &stackSet){
      set<Function *> s1;
      if(PHINode * phi = dyn_cast<PHINode>(val)){
              //errs()<<"this is phi\n";
          for(unsigned int i=0;i<phi->getNumIncomingValues();i++){
              BasicBlock * block = phi->getIncomingBlock(i);
              if(parent.count(block)){
                  set<Function *> resultSet = ParseValue(parent,phi->getIncomingValue(i),args,stackSet);
                  for(auto it = resultSet.begin();it!=resultSet.end();++it){
                      s1.insert(*it);
                  }
              }
          }
      }else if(Function * func = dyn_cast<Function>(val)){
              //errs()<<"this is function\n";
          s1.insert(func);
      }else if(Argument * arg = dyn_cast<Argument>(val)){
              //errs()<<"this is arg["<<arg->getArgNo()<<"]\n";
          set<Function *> & argset = args[arg->getArgNo()];
          for(auto it = argset.begin();it != argset.end();++it){
              s1.insert(*it);
          }
      }else if(CallInst * callinst = dyn_cast<CallInst>(val)){
              //errs()<<"this is callinst\n";
          return ParseCallInst(parent,callinst,args,stackSet);
      }else if(LoadInst * loadinst = dyn_cast<LoadInst>(val)){
              //errs()<<"load inst\n";
          Value * PointerOP = loadinst->getPointerOperand();
          if(stackSet.find(PointerOP) != stackSet.end()){
              return stackSet[PointerOP];
          }
      }
      return s1;
  }
  void ParseBlock(BasicBlock * block,set<BasicBlock*> parent,set<Function *>* ret,vector<set<Function *>> &args,map<Value*,set<Function*>> stackSet ){
          // errs()<<"begin parse block,current path:\n";
          // for(auto it = parent.begin();it != parent.end();++it){
          //     if(it != parent.begin())
          //         errs()<<"  ";
          //     errs()<<"["<<((*it)->getName())<<"]";
          // }
          // errs()<<"  (current)["<<(block->getName())<<"]\n";
      parent.insert(block);
      
      for(auto it = block->begin();it != block->end();++it){
          if(dyn_cast<DbgInfoIntrinsic>(&*it)){
              continue;
          }
          BranchInst * branch = dyn_cast<BranchInst>(&*it);
          if(branch){
              auto successors = branch->successors();
              for(auto si = successors.begin();si != successors.end();++si){
                  BasicBlock * b = *si;
                  //dfs
                  if(parent.count(b) == 0){
                      ParseBlock(b,parent,ret,args,stackSet);
                  }
              }
          }

          if(ReturnInst * setinst = dyn_cast<ReturnInst>(&*it) ){
            if(ret){
              set<Function *> ret_funcs = ParseValue(parent,setinst->getReturnValue(),args,stackSet);
              for(auto it = ret_funcs.begin();it != ret_funcs.end();++it){
                ret->insert(*it);
              }
            }
          }

          if(CallInst * call_inst = dyn_cast<CallInst>(&*it)){
              ParseCallInst(parent,call_inst,args,stackSet);
          }

          //pointOperator TODO
          if(StoreInst * store_inst = dyn_cast<StoreInst>(&*it)){
              set<Function *> funcs = ParseValue(parent,store_inst->getValueOperand(),args,stackSet);
              Value * PointerOP = store_inst->getPointerOperand();
              stackSet[PointerOP] = funcs;
          }
      }

  }
  set<Function *> Parse(Function * Fun,vector<set<Function *> > args,map<Value*,set<Function*>> stackSet){
      if(funcSet.count(Fun) == 0){
          return set<Function*>();
      }
          // errs()<<"begin parse "<<
          // F->getName()<<"\n";

      set<Function *> ret,*ret_ptr = nullptr;
      if(Fun->getReturnType()->isPointerTy()&&Fun->getReturnType()->getPointerElementType()->isFunctionTy()){
          ret_ptr = &ret;
      }else{}
      ParseBlock(&Fun->getEntryBlock(),set<BasicBlock*>(),ret_ptr,args,stackSet);

      return ret;
  }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
   	
   ///Remove functions' optnone attribute in LLVM5.0
   #if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
   #endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
}


#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include <string>

using namespace llvm;

namespace{
    struct branchBiasPass:public FunctionPass {
        static char ID;
        branchBiasPass() : FunctionPass(ID) {}

        //second and right implementation approach
        bool runOnFunction(Function &F) override {
            Module* mod=F.getParent();      //get the module that contains function F
            LLVMContext &context=mod->getContext();     //get module context (what's the difference between mod->getContext() and F.getContext())
            
            for(auto B=F.begin(), BEnd=F.end();B!=BEnd;B++){
                for(auto I=B->begin(),IEnd=B->end();I!=IEnd;I++){
                    if (isa<ReturnInst>(I)) {           //if current instruction is Return, then insert the "printOutBranchInfo" call. There maybe multiple return in function, but in runtime only one Return will be taken, thus "printOutBranchInfo" will only be called once as desired.
                        IRBuilder<> Builder(&*I);       //insert function call before return instruction
                        FunctionCallee printInstr=mod->getOrInsertFunction("printOutBranchInfo",Type::getVoidTy(context));  //create function handle
                        Builder.CreateCall(printInstr);
                    }
                    BranchInst *BI=dyn_cast<BranchInst>(I);     //try to dynamically cast pointer of instruction class instance to pointer of subclass BranchInst class instance
                    if(BI!=nullptr){    //if current instruction isn't branch, then dyn_cast will generate nullptr
                        if(BI->isConditional()==true){     //we only deal with conditional branch
                            IRBuilder<> Builder(&*BI);
                            Value* branchRes=BI->getCondition();    //getCondition() returns the reference of the result of branch, so send that to lib function call so that it can dynamically get the result of branch 
                            std::vector<Value*> arg;       // CreatCall only takes ArrayRef param, thus create a vector to contain all params of function then convert to ArrayRef
                            arg.push_back(branchRes);
                            ArrayRef<Value*> argRef(arg);
                            FunctionCallee update=mod->getOrInsertFunction("updateBranchInfo",Type::getVoidTy(context),Type::getInt1Ty(context));  //create function handle
                            Builder.CreateCall(update,argRef);       //insert the function

                        }
                    }
                }
            }  
            return false;
        }
        
        /* first implementation approach, it doesn't use the reference of existing branch result so it's more complicated. What's more there is some minor bugs, which makes it can pass the bubble sort testcase 
        bool runOnFunction(Function &F) override {
            Module* mod=F.getParent();      //get the module that contains function F
            LLVMContext &context=mod->getContext();     //get module context (what's the difference between mod->getContext() and F.getContext())
            
            for(auto B=F.begin(), BEnd=F.end();B!=BEnd;B++){
                for(auto I=B->begin(),IEnd=B->end();I!=IEnd;I++){
                    if (isa<ReturnInst>(I)) {           //if current instruction is Return, then insert the "printOutBranchInfo" call. There maybe multiple return in function, but in runtime only one Return will be taken, thus "printOutBranchInfo" will only be called once as desired.
                        IRBuilder<> Builder(&*I);       //insert function call before return instruction
                        FunctionCallee printInstr=mod->getOrInsertFunction("printOutBranchInfo",Type::getVoidTy(context));  //create function handle
                        Builder.CreateCall(printInstr);
                    }
                    BranchInst *BI=dyn_cast<BranchInst>(I);     //try to dynamically cast pointer of instruction class instance to pointer of subclass BranchInst class instance
                    if(BI!=nullptr){    //if current instruction isn't branch, then dyn_cast will generate nullptr
                        
                        if(BI->isConditional()==true){     //we only deal with conditional branch

                            // get corresponding taken block and insert "updateBranchInfo" call
                            BasicBlock* takenBlock=BI->getSuccessor(0);     //first successor is the taken block
                            Instruction &firstTakenInstr=takenBlock->front();
                            IRBuilder<> takenBuilder(&firstTakenInstr);     //insert the call before the first instruction in the taken block
                            ConstantInt* taken =takenBuilder.getInt1(1);    //indicate branch is taken with flag=1
                            std::vector<Value*> takenArg;       // CreatCall only takes ArrayRef param, thus create a vector to contain all params of function then convert to ArrayRef
                            takenArg.push_back(taken);
                            ArrayRef<Value*> takenArgRef(takenArg);
                            FunctionCallee takenInsert=mod->getOrInsertFunction("updateBranchInfo",Type::getVoidTy(context),Type::getInt1Ty(context));  //create function handle
                            takenBuilder.CreateCall(takenInsert,takenArgRef);       //insert the function

                            // get corresponding non-taken block and insert "updateBranchInfo" call
                            BasicBlock* nonTakenBlock=BI->getSuccessor(1);
                            Instruction &firstNonTakenInstr=nonTakenBlock->front();
                            IRBuilder<> nonTakenBuilder(&firstNonTakenInstr);  
                            ConstantInt* nonTaken =nonTakenBuilder.getInt1(0);
                            std::vector<Value*> nonTakenArg;
                            nonTakenArg.push_back(nonTaken);
                            ArrayRef<Value*> nonTakenArgRef(nonTakenArg);
                            FunctionCallee nonTakenInsert=mod->getOrInsertFunction("updateBranchInfo",Type::getVoidTy(context),Type::getInt1Ty(context));  //Create function handle
                            nonTakenBuilder.CreateCall(nonTakenInsert,nonTakenArgRef);
                        }
                    }
                }
            }  
            return false;
        }
        */
        
    };
}

char branchBiasPass::ID = 0;
static RegisterPass<branchBiasPass> X("cse231-bb", "Developed to dynamically summarize the bias of conditional branches", false /* Only looks at CFG */, false /* Analysis Pass */);

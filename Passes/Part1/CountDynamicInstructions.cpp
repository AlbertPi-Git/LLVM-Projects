#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include <unordered_map>
#include <string>

using namespace llvm;

namespace{
    struct countInstrPass:public FunctionPass {
        static char ID;
        countInstrPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            Module* mod=F.getParent();      //get the module that contains function F
            LLVMContext &context=mod->getContext();     //get module context (what's the difference between mod->getContext() and F.getContext())
            
            for(auto B=F.begin(), BEnd=F.end();B!=BEnd;B++){
                std::unordered_map<int,int> dic;
                std::vector<int> keys;
                std::vector<int> values;
                /* in each block, we can statically count the number of instruction in compile time, then use these static information to update global counter by inserting function call the will dynamically executed in runtime*/
                for(auto I=B->begin(),IEnd=B->end();I!=IEnd;I++){
                    if(dic.find(I->getOpcode())==dic.end()){
                        dic[I->getOpcode()]=1;
                    }else{
                        dic[I->getOpcode()]+=1;
                    }
                }
                for(auto pair:dic){
                    keys.push_back(pair.first);
                    values.push_back(pair.second);
                }
                
                /* the place to insert function call is important, can't use Builder(&*B) since this will insert some codes even after the block that contains Return, which will cause unterminated function */
                Instruction &lastI=B->back();
                IRBuilder<> Builder(&lastI);   //thus we should insert the function call before the last instruction in this block, thus Return will happen normally

                ConstantInt *Length = Builder.getInt16(dic.size());     //first param

                ArrayType* ArrayTy = ArrayType::get(IntegerType::get(F.getContext(), 32), dic.size());   //define the array type, is F.getContext() the same with F.getParent()->getContext() here?

                GlobalVariable* GlobalOpcodeArray = new GlobalVariable(*mod,ArrayTy,false,GlobalValue::ExternalLinkage,ConstantDataArray::get(context,keys),"Opcode Array");    //second param
                Value* OpcodeArrayPtr = Builder.CreatePointerCast(GlobalOpcodeArray, Type::getInt32PtrTy(context));

                GlobalVariable* GlobalCountArray = new GlobalVariable(*mod,ArrayTy,false,GlobalValue::ExternalLinkage,ConstantDataArray::get(context,values),"Count Array");    //third param
                Value* CountArrayPtr = Builder.CreatePointerCast(GlobalCountArray, Type::getInt32PtrTy(context));

                FunctionCallee countInstrInBlock=mod->getOrInsertFunction("updateInstrInfo",Type::getVoidTy(context),Type::getInt16Ty(context),Type::getInt32PtrTy(context),Type::getInt32PtrTy(context));  //create function handle
                
                std::vector<Value*> args;       // CreatCall only takes ArrayRef param, thus create a vector to contain all params of function then convert it to ArrayRef
                args.push_back(Length);
                args.push_back(OpcodeArrayPtr);
                args.push_back(CountArrayPtr);
                ArrayRef<Value*> argRef(args);

                Builder.CreateCall(countInstrInBlock,argRef);       //insert the function
            }

            /* insert the print function before the last instruction */
            BasicBlock &lastB=F.back();
            Instruction &lastI=lastB.back();
            IRBuilder<> Builder(&lastI);        
            FunctionCallee printInstr=mod->getOrInsertFunction("printOutInstrInfo",Type::getVoidTy(context));  //create function handle
            Builder.CreateCall(printInstr);
            
            return false;
        }
    };
}

char countInstrPass::ID = 0;
static RegisterPass<countInstrPass> X("cse231-cdi", "Developed to dynamically count the number of instructions in runtime", false /* Only looks at CFG */, false /* Analysis Pass */);

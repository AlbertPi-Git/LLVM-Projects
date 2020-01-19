#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include <unordered_map>
#include <string>

using namespace llvm;

namespace{
    struct countInstrPass:public FunctionPass {
        static char ID;
        countInstrPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            std::unordered_map <std::string,int> dic;
            for(inst_iterator I=inst_begin(F),End=inst_end(F);I!=End;I++){
                std::string instrName=I->getOpcodeName();
                if(dic.find(instrName)==dic.end()){
                    dic[instrName]=1;
                }else{
                    dic[instrName]=dic[instrName]+1;
                }
            }
            std::unordered_map<std::string,int>::iterator itr;
            for(itr=dic.begin();itr!=dic.end();itr++){
                errs()<<itr->first<<'\t'<<itr->second<<'\n';
            }
            return false;
        }
    };
}

char countInstrPass::ID = 0;
static RegisterPass<countInstrPass> X("cse231-csi", "Developed to statically count the number of instructions", false /* Only looks at CFG */, false /* Analysis Pass */);

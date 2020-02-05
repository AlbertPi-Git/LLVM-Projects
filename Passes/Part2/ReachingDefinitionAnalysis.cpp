#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include <unordered_set>

using namespace llvm;

namespace{
    //define a subclass of Info: ReachingInfo
    class ReachingInfo: public Info 
    {
        public:
            //Use hashset to contain the reaching definition of each edge
            std::unordered_set<unsigned> reachingDefs;

            ReachingInfo(){}
            ReachingInfo(const ReachingInfo &other):Info(other){
                reachingDefs=other.reachingDefs;
            }
            //Implement virtual function of parent class to print reaching definition
            void print(){
                for(auto iter:reachingDefs){
                    errs()<<iter<<"|";
                }
                errs()<<"\n";
            }
            //Implement equal function 
            static bool equals(ReachingInfo* info1, ReachingInfo* info2){
                bool res=true;
                for(auto iter:info1->reachingDefs){
                    if(info2->reachingDefs.find(iter)==info2->reachingDefs.end()){
                        res=false;
                        break;
                    }
                }
                return res;
            }
            //Use set_union function to implement join() function
            static ReachingInfo* join(ReachingInfo* info1, ReachingInfo* info2, ReachingInfo* result){
                std::set_union(info1->reachingDefs.begin(),info1->reachingDefs.end(),info2->reachingDefs.begin(),info2->reachingDefs.end(),std::inserter(result->reachingDefs,result->reachingDefs.end()));
                return result;
            }
    };
    //define a subclass of DataFlowAnalysis: ReachingDefinitionAnalysis
    class ReachingDefinitionAnalysis: public DataFlowAnalysis<ReachingInfo,true> {
        private:
            //Implement flowfunction to process three types of instructions
            void flowfunction(Instruction * I,std::vector<unsigned> & IncomingEdges,std::vector<unsigned> & OutgoingEdges,std::vector<ReachingInfo *> & InfoOut){
                unsigned nodeIndex=InstrToIndex[I];
                std::string instrName=I->getOpcodeName();
                int instrType;
                // 1st type is instruction that define a variable in IR code, 2nd type is instruction that doesn't define variable, 3rd type is phi instruction (specifically all successive phi instructions are condiered as a whole node, which means this type of instruction will define many variables "at the same time")   
                if(instrName=="add"||instrName=="fadd"||instrName=="sub"||instrName=="fsub"||instrName=="mul"||instrName=="fmul"||instrName=="udiv"||instrName=="sdiv"||instrName=="fdiv"||instrName=="urem"||instrName=="srem"||instrName=="frem"||instrName=="shl"||instrName=="lshr"||instrName=="ashr"||instrName=="and"||instrName=="or"||instrName=="xor"||instrName=="icmp"||instrName=="fcmp"||instrName=="select"||instrName=="alloca"||instrName=="load"||instrName=="getelementptr"){
                    instrType=1;
                }else if(instrName=="br"||instrName=="store"){
                    instrType=2;
                }else if(instrName=="phi"){
                    instrType=3;
                }else{
                    instrType=2;
                }
                //Join all infos on all incomingEdges
                ReachingInfo AllInfoIn;
                for(auto edgeIndex: IncomingEdges){
                    ReachingInfo* tmpInfo=EdgeToInfo[std::make_pair(edgeIndex,nodeIndex)];
                    ReachingInfo::join(&AllInfoIn,tmpInfo,&AllInfoIn);
                }
                //if it's 1st type instruction, then add the index of this instruction to the set of incoming information
                if(1==instrType){
                    AllInfoIn.reachingDefs.insert(nodeIndex);
                }else if(3==instrType){         //if it's 3rd type instruction, join the set of all successive phi instructions with the set of incoming information
                    BasicBlock * parentBlock=I->getParent();    //get the block that the first phi instruction belongs to
                    unsigned nonPhiIndex=InstrToIndex[parentBlock->getFirstNonPHI()];       //get the index of the first Non-phi instruction
                    for(unsigned i=nodeIndex;i<nonPhiIndex;i++){    //Add all indices between them to the incoming information set
                        AllInfoIn.reachingDefs.insert(i);
                    }
                }
                //put the output reachingInfo to the result container
                InfoOut[0]->reachingDefs=AllInfoIn.reachingDefs;
            }
        public:
            //the constructor which explicitly call the constructor of parent class
            ReachingDefinitionAnalysis(ReachingInfo& bottom, ReachingInfo& initialState):DataFlowAnalysis(bottom,initialState){}
    };

    struct ReachingDefinitionAnalysisPass:public FunctionPass {
        static char ID;
        ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            //define bottom and initialState in lattice
            ReachingInfo bottom=ReachingInfo();
            ReachingInfo initialState=ReachingInfo();
            ReachingDefinitionAnalysis ReachDefAnalysis=ReachingDefinitionAnalysis(bottom,initialState);

            ReachDefAnalysis.runWorklistAlgorithm(&F);  //Use the worklist algorithm to analyze the reaching definition 
            ReachDefAnalysis.print();   //Print result

            return false;
        }
    };
}

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", "Developed to analyze reaching definition", false /* Only looks at CFG */, false /* Analysis Pass */);
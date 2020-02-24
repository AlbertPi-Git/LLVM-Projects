#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include <set>
#include <iostream>

using namespace llvm;

namespace{
    //define a subclass of Info: LivenessInfo
    class LivenessInfo: public Info 
    {
        public:
            //Use hashset to contain the reaching definition of each edge
            std::set<unsigned> LivenessDefs;

            LivenessInfo(){}
            LivenessInfo(const LivenessInfo &other):Info(other){
                LivenessDefs=other.LivenessDefs;
            }
            //Implement virtual function of parent class to print reaching definition
            void print(){
                for(auto iter:LivenessDefs){
                    errs()<<iter<<"|";
                }
                errs()<<"\n";
            }
            //Implement equal function 
            static bool equals(LivenessInfo* info1, LivenessInfo* info2){
                bool res=true;
                for(auto iter:info1->LivenessDefs){
                    if(info2->LivenessDefs.find(iter)==info2->LivenessDefs.end()){
                        res=false;
                        break;
                    }
                }
                return res;
            }
            //Use set_union function to implement join() function
            static LivenessInfo* join(LivenessInfo* info1, LivenessInfo* info2, LivenessInfo* result){
                std::set_union(info1->LivenessDefs.begin(),info1->LivenessDefs.end(),info2->LivenessDefs.begin(),info2->LivenessDefs.end(),std::inserter(result->LivenessDefs,result->LivenessDefs.end()));
                return result;
            }
    };
    //define a subclass of DataFlowAnalysis: LivenessAnalysis
    class LivenessAnalysis: public DataFlowAnalysis<LivenessInfo,false> {
        private:
            //Implement flowfunction to process three types of instructions
            void flowfunction(Instruction * I,std::vector<unsigned> & IncomingEdges,std::vector<unsigned> & OutgoingEdges,std::vector<LivenessInfo *> & InfoOut){
                unsigned curNodeIndex=InstrToIndex[I];
                std::string instrName=I->getOpcodeName();
                int instrType;
                // 1st type is instruction that define a variable in IR code, 2nd type is instruction that doesn't define variable, 3rd type is phi instruction (specifically all successive phi instructions are condiered as a whole node, which means this type of instruction will define many variables "at the same time")   
                if(instrName=="add"||instrName=="fadd"||instrName=="sub"||instrName=="fsub"||instrName=="mul"||instrName=="fmul"||instrName=="udiv"||instrName=="sdiv"||instrName=="fdiv"||instrName=="urem"||instrName=="srem"||instrName=="frem"||instrName=="shl"||instrName=="lshr"||instrName=="ashr"||instrName=="and"||instrName=="or"||instrName=="xor"||instrName=="icmp"||instrName=="fcmp"||instrName=="select"||instrName=="alloca"||instrName=="load"||instrName=="getelementptr"){
                    instrType=1;
                }else if(instrName=="phi"){
                    instrType=3;
                }else{
                    instrType=2;
                }
                //Join all infos on all incomingEdges
                LivenessInfo AllInfoIn;
                for(auto incomingNodeIndex: IncomingEdges){
                    LivenessInfo* tmpInfo=EdgeToInfo[std::make_pair(incomingNodeIndex,curNodeIndex)];
                    LivenessInfo::join(&AllInfoIn,tmpInfo,&AllInfoIn);
                }
                //if it's 1st or 2nd type instruction, then add the index of operands to the set of incoming information. For the 1st type instruction, remove the index of result from incoming information.
                if(1==instrType||2==instrType){
                    unsigned operandNum=I->getNumOperands();
                    //Remove the index of current instruction if it defines a new variable
                    if(1==instrType)
                        AllInfoIn.LivenessDefs.erase(curNodeIndex);     //??erase may need to be moved to the front of insert. And we shouldn't modify the incoming info. Rather we should copy it to info out, then modify

                    //Add indices of instructions where operands are defined 
                    for(unsigned i=0;i<operandNum;++i){
                        if(false==isa<Constant>(I->getOperand(i))){ 
                            Instruction* OperandInstr=dyn_cast<Instruction>(I->getOperand(i));
                            AllInfoIn.LivenessDefs.insert(InstrToIndex[OperandInstr]);
                        }
                    }
                    
                    //put the output reachingInfo to the result container
                    for(unsigned i=0;i<InfoOut.size();++i){
                        InfoOut[i]->LivenessDefs=AllInfoIn.LivenessDefs;
                    }
                }else if(3==instrType){         //if it's 3rd type instruction, join the set of all successive phi instructions with the set of incoming information
                    BasicBlock * parentBlock=I->getParent();    //get the block that the first phi instruction belongs to
                    unsigned nonPhiIndex=InstrToIndex[parentBlock->getFirstNonPHI()];       //get the index of the first Non-phi instruction
                    for(unsigned i=curNodeIndex;i<nonPhiIndex;++i){    //remove all indices between them from the incoming information set, since they represent of definition of results they generate.
                        AllInfoIn.LivenessDefs.erase(i);
                    }
                    for(unsigned i=0;i<InfoOut.size();++i){     //Iterate through all outgoing edges
                        InfoOut[i]->LivenessDefs=AllInfoIn.LivenessDefs;    
                        for(unsigned j=curNodeIndex;j<nonPhiIndex;++j){     //For each outgoing edge, iterate through phi nodes
                            PHINode* curPhiNode=dyn_cast<PHINode>(IndexToInstr[j]);
                            unsigned PhiOperandNum=curPhiNode->getNumIncomingValues();  //Get how many operands (value,block pairs) this phi node has
                            for(unsigned k=0;k<PhiOperandNum;++k){      //Iterate through all pairs
                                BasicBlock* operandBlock=curPhiNode->getIncomingBlock(k);   //Which block does this pair go
                                if(operandBlock==IndexToInstr[OutgoingEdges[i]]->getParent()){  //The value will be added to the info set only when the block this pair goes equals to the block this outgoing edge go
                                    Value* operandValue=curPhiNode->getIncomingValue(k);
                                    Instruction* OperandInstr=dyn_cast<Instruction>(operandValue);  //Get the instruction where the value in the pair is defined
                                    (InfoOut[i]->LivenessDefs).insert(InstrToIndex[OperandInstr]);  //Add it to the info set.
                                }
                            }
                        }
                    }
                }
            }
        public:
            //the constructor which explicitly call the constructor of parent class
            LivenessAnalysis(LivenessInfo& bottom, LivenessInfo& initialState):DataFlowAnalysis(bottom,initialState){}
    };

    struct LivenessAnalysisPass:public FunctionPass {
        static char ID;
        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            //define bottom and initialState in lattice
            LivenessInfo bottom=LivenessInfo();
            LivenessInfo initialState=LivenessInfo();
            LivenessAnalysis ReachDefAnalysis=LivenessAnalysis(bottom,initialState);

            ReachDefAnalysis.runWorklistAlgorithm(&F);  //Use the worklist algorithm to analyze the reaching definition 
            ReachDefAnalysis.print();   //Print result

            return false;
        }
    };
}

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", "Developed to analyze liveness of variables", false /* Only looks at CFG */, false /* Analysis Pass */);

